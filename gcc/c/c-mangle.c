/* Name mangling for C overloadable attribute feature.
   Copyright (C) 2016-2016 Free Software Foundation, Inc.
   Written by Yu Xuanchi <yuxuanchiadm@126.com>

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify it under
the terms of the GNU General Public License as published by the Free
Software Foundation; either version 3, or (at your option) any later
version.

GCC is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
for more details.

You should have received a copy of the GNU General Public License
along with GCC; see the file COPYING3.  If not see
<http://www.gnu.org/licenses/>.  */

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "target.h"
#include "c-tree.h"
#include "stringpool.h"
#include "stor-layout.h"
#include "attribs.h"
#include "c-mangle.h"

#define OVERLOAD_TYPE_P(T) \
  (TREE_CODE (type) == ENUMERAL_TYPE \
  || TREE_CODE(type) == RECORD_TYPE \
  || TREE_CODE(type) == UNION_TYPE)

/* Things we only need one of.  This module is not reentrant.  */
struct GTY(()) c_mangle_globals {
  /* An array of the current substitution candidates, in the order
     we've seen them.  */
  vec<tree, va_gc> *substitutions;
};

static GTY (()) c_mangle_globals G;

/* The obstack on which we build mangled names.  */
static struct obstack *mangle_obstack;

/* The obstack on which we build mangled names that are not going to
   be IDENTIFIER_NODEs.  */
static struct obstack name_obstack;

/* The first object on the name_obstack; we use this to free memory
   allocated on the name_obstack.  */
static void *name_base;

/* Single-letter codes for builtin integer types, defined in
   <builtin-type>.  These are indexed by integer_type_kind values.  */
static const char
integer_type_codes[itk_none] =
{
  'c',  /* itk_char */
  'a',  /* itk_signed_char */
  'h',  /* itk_unsigned_char */
  's',  /* itk_short */
  't',  /* itk_unsigned_short */
  'i',  /* itk_int */
  'j',  /* itk_unsigned_int */
  'l',  /* itk_long */
  'm',  /* itk_unsigned_long */
  'x',  /* itk_long_long */
  'y',  /* itk_unsigned_long_long */
  /* __intN types are handled separately */
  '\0', '\0', '\0', '\0', '\0', '\0', '\0', '\0'
};

/* Functions for handling substitutions.  */

static inline tree canonicalize_for_substitution (tree);
static void add_substitution (tree);
static int find_substitution (tree);

/* Functions for emitting mangled representations of things.  */

static tree get_mangled_id (tree decl);
static void write_mangled_name (const tree, bool);
static void write_encoding (const tree);
static void write_name (tree);
static void write_unscoped_name (const tree);
static void write_unqualified_id (tree);
static void write_unqualified_name (tree);
static void write_source_name (tree);
static int hwint_to_ascii (unsigned HOST_WIDE_INT, const unsigned int, char *,
			   const unsigned int);
static void write_number (unsigned HOST_WIDE_INT, const int,
			  const unsigned int);
static void write_type (tree);
static int write_CV_qualifiers_for_type (const tree);
static void write_builtin_type (tree);
static void write_function_type (const tree);
static void write_bare_function_type (const tree, const int);
static void write_method_parms (tree parm_types);
static void write_class_enum_type (const tree);
static void write_array_type (const tree);
static void write_substitution (const int);
static tree mangle_decl_string (const tree);

/* Control functions.  */

static inline void start_mangling (void);
static inline const char * finish_mangling (void);
static tree finish_mangling_get_identifier (void);

/* Utility functions.  */
static bool unmangled_name_p (const tree);
static bool tx_safe_fn_type_p (tree);

/* Append a single character to the end of the mangled
   representation.  */
#define write_char(CHAR)						\
  obstack_1grow (mangle_obstack, (CHAR))

/* Append a sized buffer to the end of the mangled representation.  */
#define write_chars(CHAR, LEN)						\
  obstack_grow (mangle_obstack, (CHAR), (LEN))

/* Append a NUL-terminated string to the end of the mangled
   representation.  */
#define write_string(STRING)						\
  obstack_grow (mangle_obstack, (STRING), strlen (STRING))

/* Write out an unsigned quantity in base 10.  */
#define write_unsigned_number(NUMBER)					\
  write_number ((NUMBER), /*unsigned_p=*/1, 10)

/* Both decls and types can be substitution candidates, but sometimes
   they refer to the same thing.  For instance, a TYPE_DECL and
   RECORD_TYPE for the same class refer to the same thing, and should
   be treated accordingly in substitutions.  This function returns a
   canonicalized tree node representing NODE that is used when adding
   and substitution candidates and finding matches.  */

static inline tree
canonicalize_for_substitution (tree node)
{
  /* For a TYPE_DECL, use the type instead.  */
  if (TREE_CODE (node) == TYPE_DECL)
    node = TREE_TYPE (node);
  if (TYPE_P (node)
      && TYPE_CANONICAL (node) != node
      && TYPE_MAIN_VARIANT (node) != node)
    {
	node = build_qualified_type (TYPE_MAIN_VARIANT (node),
				     TYPE_QUALS (node));
    }
  return node;
}

/* Add NODE as a substitution candidate.  NODE must not already be on
   the list of candidates.  */

static void
add_substitution (tree node)
{
  tree c;

  /* Get the canonicalized substitution candidate for NODE.  */
  c = canonicalize_for_substitution (node);
  node = c;

  /* Make sure NODE isn't already a candidate.  */
  if (flag_checking)
	{
	  int i;
	  tree candidate;

	  FOR_EACH_VEC_SAFE_ELT (G.substitutions, i, candidate)
	{
	  gcc_assert (!(DECL_P (node) && node == candidate));
	  gcc_assert (!(TYPE_P (node) && TYPE_P (candidate)
			  && comptypes (node, candidate)));
	}
	}

  /* Put the decl onto the varray of substitution candidates.  */
  vec_safe_push (G.substitutions, node);
}

/* Check whether a substitution should be used to represent NODE in
   the mangling.

   Examine the stack of currently available substitution
   candidates for entities appearing earlier in the same mangling

   If a substitution is found, write its mangled representation and
   return nonzero.  If none is found, just return zero.  */

static int
find_substitution (tree node)
{
  int i;
  const int size = vec_safe_length (G.substitutions);
  tree decl;
  tree type;

  /* Obtain the canonicalized substitution representation for NODE.
     This is what we'll compare against.  */
  node = canonicalize_for_substitution (node);

  decl = TYPE_P (node) ? TYPE_NAME (node) : node;
  type = TYPE_P (node) ? node : TREE_TYPE (node);

  /* Now check the list of available substitutions for this mangling
     operation.  */
  for (i = 0; i < size; ++i)
    {
      tree candidate = (*G.substitutions)[i];
      /* NODE is a matched to a candidate if it's the same decl node or
	 if it's the same type.  */
      if (decl == candidate
	  || (TYPE_P (candidate) && type && TYPE_P (node)
	      && comptypes (type, candidate)))
	{
	  write_substitution (i);
	  return 1;
	}
    }

  /* No substitution found.  */
  return 0;
}

/* Returns whether DECL's symbol name should be the plain unqualified-id
   rather than a more complicated mangled name.  */

static bool
unmangled_name_p (const tree decl)
{
  /* Only functions are mangled.  */
  if (TREE_CODE (decl) == FUNCTION_DECL)
    {
      /* Declarations with overloadable are mangled.  */
      if (lookup_attribute ("overloadable", DECL_ATTRIBUTES (decl)))
	return false;

	  /* Others are not mangled.  */
	  return true;
	}

  return true;
}

/* TOP_LEVEL is true, if this is being called at outermost level of
  mangling. It should be false when mangling a decl appearing in an
  expression within some other mangling.

  <mangled-name>      ::= _Z <encoding>  */

static void
write_mangled_name (const tree decl, bool top_level)
{
  if (unmangled_name_p (decl))
    {
      if (top_level)
	write_string (IDENTIFIER_POINTER (DECL_NAME (decl)));
      else
	{
	  /* The standard notes: "The <encoding> of an extern "C"
	     function is treated like global-scope data, i.e. as its
	     <source-name> without a type."  We cannot write
	     overloaded operators that way though, because it contains
	     characters invalid in assembler.  */
	  write_string ("_Z");
	  write_source_name (DECL_NAME (decl));
	}
    }
  else
    {
      write_string ("_Z");
      write_encoding (decl);
    }
}

/* <encoding> ::= <function name> <bare-function-type>  */

static void
write_encoding (const tree decl)
{
  write_source_name (DECL_NAME (decl));

  if (TREE_CODE (decl) == FUNCTION_DECL)
    {
      tree fn_type;

      fn_type = TREE_TYPE (decl);
      write_bare_function_type (fn_type,
				0);
	}
}

/* <name> ::= <unscoped-name>  */

static void
write_name (tree decl)
{
  if (TREE_CODE (decl) == TYPE_DECL)
    {
      /* In case this is a typedef, fish out the corresponding
	 TYPE_DECL for the main variant.  */
      decl = TYPE_NAME (TYPE_MAIN_VARIANT (TREE_TYPE (decl)));
    }

  write_unscoped_name (decl);
}

/* <unscoped-name> ::= <unqualified-name>  */

static void
write_unscoped_name (const tree decl)
{
  write_unqualified_name (decl);
}

/* <unqualified-name>  ::= <source-name>  */

static void
write_unqualified_id (tree identifier)
{
  write_source_name (identifier);
}

static void
write_unqualified_name (tree decl)
{
  if (TREE_CODE (decl) == IDENTIFIER_NODE)
    {
      write_unqualified_id (decl);
      return;
    }

  if (DECL_NAME (decl) == NULL_TREE)
    {
      gcc_assert (DECL_ASSEMBLER_NAME_SET_P (decl));
      write_source_name (DECL_ASSEMBLER_NAME (decl));
    }
  else
    {
      write_source_name (DECL_NAME (decl));
    }
}

/* Non-terminal <source-name>.  IDENTIFIER is an IDENTIFIER_NODE.

     <source-name> ::= </length/ number> <identifier>  */

static void
write_source_name (tree identifier)
{
  write_unsigned_number (IDENTIFIER_LENGTH (identifier));
  write_string (IDENTIFIER_POINTER (identifier));
}

/* Convert NUMBER to ascii using base BASE and generating at least
   MIN_DIGITS characters. BUFFER points to the _end_ of the buffer
   into which to store the characters. Returns the number of
   characters generated (these will be laid out in advance of where
   BUFFER points).  */

static int
hwint_to_ascii (unsigned HOST_WIDE_INT number, const unsigned int base,
		char *buffer, const unsigned int min_digits)
{
  static const char base_digits[] = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ";
  unsigned digits = 0;

  while (number)
    {
      unsigned HOST_WIDE_INT d = number / base;

      *--buffer = base_digits[number - d * base];
      digits++;
      number = d;
    }
  while (digits < min_digits)
    {
      *--buffer = base_digits[0];
      digits++;
    }
  return digits;
}

/* Non-terminal <number>.

     <number> ::= [n] </decimal integer/>  */

static void
write_number (unsigned HOST_WIDE_INT number, const int unsigned_p,
	      const unsigned int base)
{
  char buffer[sizeof (HOST_WIDE_INT) * 8];
  unsigned count = 0;

  if (!unsigned_p && (HOST_WIDE_INT) number < 0)
    {
      write_char ('n');
      number = -((HOST_WIDE_INT) number);
    }
  count = hwint_to_ascii (number, base, buffer + sizeof (buffer), 1);
  write_chars (buffer + sizeof (buffer) - count, count);
}

/* Non-terminal <function-type>.  NODE is a FUNCTION_TYPE or
   METHOD_TYPE.  The return type is mangled before the parameter
   types.

     <function-type> ::= F [Y] <bare-function-type> E   */

static void
write_function_type (const tree type)
{
  if (tx_safe_fn_type_p (type))
    write_string ("Dx");

  write_char ('F');

  write_bare_function_type (type, /*include_return_type_p=*/1);

  write_char ('E');
}

/* Non-terminal <bare-function-type>. If INCLUDE_RETURN_TYPE is nonzero,
   the return value is mangled before the parameter types. If non-NULL,
   DECL is FUNCTION_DECL for the function whose type is being emitted.

     <bare-function-type> ::= </signature/ type>+  */

static void
write_bare_function_type (const tree type, const int include_return_type_p)
{
  /* Mangle the return type, if requested.  */
  if (include_return_type_p)
    write_type (TREE_TYPE (type));

  /* Now mangle the types of the arguments.  */
  write_method_parms (TYPE_ARG_TYPES (type));
}

/* Write the mangled representation of a method parameter list of
   types given in PARM_TYPES.  */

static void
write_method_parms (tree parm_types)
{
  tree first_parm_type;

  /* Assume this parameter type list is variable-length.  If it ends
     with a void type, then it's not.  */
  int varargs_p = 1;

  for (first_parm_type = parm_types;
       parm_types;
       parm_types = TREE_CHAIN (parm_types))
    {
      tree parm = TREE_VALUE (parm_types);
      if (parm == void_type_node)
	{
	  /* "Empty parameter lists, whether declared as () or
	     conventionally as (void), are encoded with a void parameter
	     (v)."  */
	  if (parm_types == first_parm_type)
	    write_type (parm);
	  /* If the parm list is terminated with a void type, it's
	     fixed-length.  */
	  varargs_p = 0;
	  /* A void type better be the last one.  */
	  gcc_assert (TREE_CHAIN (parm_types) == NULL);
	}
      else
	write_type (parm);
    }

  if (varargs_p)
    /* <builtin-type> ::= z  # ellipsis  */
    write_char ('z');
}


/* <class-enum-type> ::= <name>  */

static void
write_class_enum_type (const tree type)
{
  write_name (TYPE_NAME (type));
}

/* Non-terminals <type> and <CV-qualifier>.

     <type> ::= <builtin-type>
	    ::= <function-type>
	    ::= <class-enum-type>
	    ::= <array-type>
	    ::= <substitution>
	    ::= <CV-qualifier>
	    ::= P <type>    # pointer-to
	    ::= C <type>    # complex pair (C 2000)
	    ::= G <type>    # imaginary (C 2000)     [not supported]
	    ::= U <source-name> <type>   # vendor extended type qualifier

   TYPE is a type node.  */

static void
write_type (tree type)
{
  /* This gets set to nonzero if TYPE turns out to be a (possibly
     CV-qualified) builtin type.  */
  int is_builtin_type = 0;

  if (type == error_mark_node)
    return;

  type = canonicalize_for_substitution (type);
  if (find_substitution (type))
    return;


  if (write_CV_qualifiers_for_type (type) > 0)
    /* If TYPE was CV-qualified, we just wrote the qualifiers; now
       mangle the unqualified type.  The recursive call is needed here
       since both the qualified and unqualified types are substitution
       candidates.  */
    {
      tree t = TYPE_MAIN_VARIANT (type);
      if (TYPE_ATTRIBUTES (t) && !OVERLOAD_TYPE_P (t))
	{
	  tree attrs = NULL_TREE;
	  if (tx_safe_fn_type_p (type))
	    attrs = tree_cons (get_identifier ("transaction_safe"),
			       NULL_TREE, attrs);
	  t = build_type_attribute_variant (t, attrs);
	}
      gcc_assert (t != type);
      if (TREE_CODE (t) == FUNCTION_TYPE)
	{
	  if (type == TYPE_MAIN_VARIANT (type))
	    /* Avoid adding the unqualified function type as a substitution.  */
	    write_function_type (t);
	  else
	    write_type (t);
	}
      else
	write_type (t);
    }
  else if (TREE_CODE (type) == ARRAY_TYPE)
    /* It is important not to use the TYPE_MAIN_VARIANT of TYPE here
       so that the cv-qualification of the element type is available
       in write_array_type.  */
    write_array_type (type);
  else
    {
      tree type_orig = type;

      /* See through any typedefs.  */
      type = TYPE_MAIN_VARIANT (type);

      /* Some library classes are passed the same as the scalar type
		 of their single member and use the same mangling.  */
      if (TREE_CODE (type) == RECORD_TYPE && TYPE_TRANSPARENT_AGGR (type))
	type = TREE_TYPE (first_field (type));

	  /* Handle any target-specific fundamental types.  */
	  const char *target_mangling
	    = targetm.mangle_type (type_orig);

	  if (target_mangling)
	    {
	      write_string (target_mangling);
	      /* Add substitutions for types other than fundamental
		 types.  */
	      if (!VOID_TYPE_P (type)
		  && TREE_CODE (type) != INTEGER_TYPE
		  && TREE_CODE (type) != REAL_TYPE
		  && TREE_CODE (type) != BOOLEAN_TYPE)
		add_substitution (type);
	      return;
	    }

	  switch (TREE_CODE (type))
	    {
	    case VOID_TYPE:
	    case BOOLEAN_TYPE:
	    case INTEGER_TYPE:  /* Includes wchar_t.  */
	    case REAL_TYPE:
	    case FIXED_POINT_TYPE:
	      {
		/* If this is a typedef, TYPE may not be one of
		   the standard builtin type nodes, but an alias of one.  Use
		   TYPE_MAIN_VARIANT to get to the underlying builtin type.  */
		write_builtin_type (TYPE_MAIN_VARIANT (type));
		++is_builtin_type;
	      }
	      break;

	    case COMPLEX_TYPE:
	      write_char ('C');
	      write_type (TREE_TYPE (type));
	      break;

	    case FUNCTION_TYPE:
	      write_function_type (type);
	      break;

	    case UNION_TYPE:
	    case RECORD_TYPE:
	    case ENUMERAL_TYPE:
	   	  write_class_enum_type (type);
	      break;

	    case POINTER_TYPE:
		  write_char ('P');
	      {
		tree target = TREE_TYPE (type);
		if (TREE_CODE (target) == FUNCTION_TYPE)
		  {
		    target = build_qualified_type (target, TYPE_UNQUALIFIED);
		  }
		write_type (target);
	      }
	      break;

	    case VECTOR_TYPE:
		  write_string ("Dv");
		  /* Non-constant vector size would be encoded with
		     _ expression, but we don't support that yet.  */
		  write_unsigned_number (TYPE_VECTOR_SUBPARTS (type));
		  write_char ('_');
	      write_type (TREE_TYPE (type));
	      break;

	    case TYPEOF_TYPE:
	      sorry ("mangling typeof");
	      break;

	    case LANG_TYPE:
	      /* fall through.  */

	    default:
	      gcc_unreachable ();
	    }
    }

  /* Types other than builtin types are substitution candidates.  */
  if (!is_builtin_type)
    add_substitution (type);
}

/* Non-terminal <CV-qualifiers> for type nodes.  Returns the number of
   CV-qualifiers written for TYPE.

     <CV-qualifiers> ::= [r] [V] [K]  */

static int
write_CV_qualifiers_for_type (const tree type)
{
  int num_qualifiers = 0;

  /* The order is specified by:

       "In cases where multiple order-insensitive qualifiers are
       present, they should be ordered 'K' (closest to the base type),
       'V' and 'r' (farthest from the base type) ..."  */

  int quals = TYPE_QUALS (type);

  if (quals & TYPE_QUAL_RESTRICT)
    {
      write_char ('r');
      ++num_qualifiers;
    }
  if (quals & TYPE_QUAL_VOLATILE)
    {
      write_char ('V');
      ++num_qualifiers;
    }
  if (quals & TYPE_QUAL_CONST)
    {
      write_char ('K');
      ++num_qualifiers;
    }

  return num_qualifiers;
}

/* Non-terminal <builtin-type>.

     <builtin-type> ::= v   # void
		    ::= b   # bool
		    ::= w   # wchar_t
		    ::= c   # char
		    ::= a   # signed char
		    ::= h   # unsigned char
		    ::= s   # short
		    ::= t   # unsigned short
		    ::= i   # int
		    ::= j   # unsigned int
		    ::= l   # long
		    ::= m   # unsigned long
		    ::= x   # long long, __int64
		    ::= y   # unsigned long long, __int64
		    ::= n   # __int128
		    ::= o   # unsigned __int128
		    ::= f   # float
		    ::= d   # double
		    ::= e   # long double, __float80
		    ::= g   # __float128          [not supported]
		    ::= u <source-name>  # vendor extended type */

static void
write_builtin_type (tree type)
{
  if (TYPE_CANONICAL (type))
    type = TYPE_CANONICAL (type);

  switch (TREE_CODE (type))
    {
    case VOID_TYPE:
      write_char ('v');
      break;

    case BOOLEAN_TYPE:
      write_char ('b');
      break;

    case INTEGER_TYPE:
      /* TYPE may still be wchar_t, char16_t, or char32_t, since that
	 isn't in integer_type_nodes.  */
      if (type == wchar_type_node)
	write_char ('w');
      else if (type == char16_type_node)
	write_string ("Ds");
      else if (type == char32_type_node)
	write_string ("Di");
      else
	{
	  size_t itk;
	  /* Assume TYPE is one of the shared integer type nodes.  Find
	     it in the array of these nodes.  */
	iagain:
	  for (itk = 0; itk < itk_none; ++itk)
	    if (integer_types[itk] != NULL_TREE
		&& integer_type_codes[itk] != '\0'
		&& type == integer_types[itk])
	      {
		/* Print the corresponding single-letter code.  */
		write_char (integer_type_codes[itk]);
		break;
	      }

	  if (itk == itk_none)
	    {
	      tree t = c_common_type_for_mode (TYPE_MODE (type),
					       TYPE_UNSIGNED (type));
	      if (type != t)
		{
		  type = t;
		  goto iagain;
		}

	      if (TYPE_PRECISION (type) == 128)
		write_char (TYPE_UNSIGNED (type) ? 'o' : 'n');
	      else
		{
		  /* Allow for cases where TYPE is not one of the shared
		     integer type nodes and write a "vendor extended builtin
		     type" with a name the form intN or uintN, respectively.
		     Situations like this can happen if you have an
		     __attribute__((__mode__(__SI__))) type and use exotic
		     switches like '-mint8' on AVR.  Of course, this is
		     undefined by the C++ ABI (and '-mint8' is not even
		     Standard C conforming), but when using such special
		     options you're pretty much in nowhere land anyway.  */
		  const char *prefix;
		  char prec[11];	/* up to ten digits for an unsigned */

		  prefix = TYPE_UNSIGNED (type) ? "uint" : "int";
		  sprintf (prec, "%u", (unsigned) TYPE_PRECISION (type));
		  write_char ('u');	/* "vendor extended builtin type" */
		  write_unsigned_number (strlen (prefix) + strlen (prec));
		  write_string (prefix);
		  write_string (prec);
		}
	    }
	}
      break;

    case REAL_TYPE:
      if (type == float_type_node)
	write_char ('f');
      else if (type == double_type_node)
	write_char ('d');
      else if (type == long_double_type_node)
	write_char ('e');
      else if (type == dfloat32_type_node)
	write_string ("Df");
      else if (type == dfloat64_type_node)
	write_string ("Dd");
      else if (type == dfloat128_type_node)
	write_string ("De");
      else
	gcc_unreachable ();
      break;

    case FIXED_POINT_TYPE:
      write_string ("DF");
      if (GET_MODE_IBIT (TYPE_MODE (type)) > 0)
	write_unsigned_number (GET_MODE_IBIT (TYPE_MODE (type)));
      if (type == fract_type_node
	  || type == sat_fract_type_node
	  || type == accum_type_node
	  || type == sat_accum_type_node)
	write_char ('i');
      else if (type == unsigned_fract_type_node
	       || type == sat_unsigned_fract_type_node
	       || type == unsigned_accum_type_node
	       || type == sat_unsigned_accum_type_node)
	write_char ('j');
      else if (type == short_fract_type_node
	       || type == sat_short_fract_type_node
	       || type == short_accum_type_node
	       || type == sat_short_accum_type_node)
	write_char ('s');
      else if (type == unsigned_short_fract_type_node
	       || type == sat_unsigned_short_fract_type_node
	       || type == unsigned_short_accum_type_node
	       || type == sat_unsigned_short_accum_type_node)
	write_char ('t');
      else if (type == long_fract_type_node
	       || type == sat_long_fract_type_node
	       || type == long_accum_type_node
	       || type == sat_long_accum_type_node)
	write_char ('l');
      else if (type == unsigned_long_fract_type_node
	       || type == sat_unsigned_long_fract_type_node
	       || type == unsigned_long_accum_type_node
	       || type == sat_unsigned_long_accum_type_node)
	write_char ('m');
      else if (type == long_long_fract_type_node
	       || type == sat_long_long_fract_type_node
	       || type == long_long_accum_type_node
	       || type == sat_long_long_accum_type_node)
	write_char ('x');
      else if (type == unsigned_long_long_fract_type_node
	       || type == sat_unsigned_long_long_fract_type_node
	       || type == unsigned_long_long_accum_type_node
	       || type == sat_unsigned_long_long_accum_type_node)
	write_char ('y');
      else
	sorry ("mangling unknown fixed point type");
      write_unsigned_number (GET_MODE_FBIT (TYPE_MODE (type)));
      if (TYPE_SATURATING (type))
	write_char ('s');
      else
	write_char ('n');
      break;

    default:
      gcc_unreachable ();
    }
}

/* Non-terminal <array-type>.  TYPE is an ARRAY_TYPE.

     <array-type> ::= A [</dimension/ number>] _ </element/ type>
		  ::= A <expression> _ </element/ type>

     "Array types encode the dimension (number of elements) and the
     element type.  For variable length arrays, the dimension (but not
     the '_' separator) is omitted."
     Note that for flexible array members, like for other arrays of
     unspecified size, the dimension is also omitted.  */

static void
write_array_type (const tree type)
{
  write_char ('A');
  if (TYPE_DOMAIN (type))
    {
      tree index_type;

      index_type = TYPE_DOMAIN (type);
      /* The INDEX_TYPE gives the upper and lower bounds of the array.
	 It's null for flexible array members which have no upper bound
	 (this is a change from GCC 5 and prior where such members were
	 incorrectly mangled as zero-length arrays).  */
      if (tree max = TYPE_MAX_VALUE (index_type))
	{
	  if (TREE_CODE (max) == INTEGER_CST)
	    {
	      /* The ABI specifies that we should mangle the number of
		 elements in the array, not the largest allowed index.  */
	      offset_int wmax = wi::to_offset (max) + 1;
	      /* Truncate the result - this will mangle [0, SIZE_INT_MAX]
		 number of elements as zero.  */
	      wmax = wi::zext (wmax, TYPE_PRECISION (TREE_TYPE (max)));
	      gcc_assert (wi::fits_uhwi_p (wmax));
	      write_unsigned_number (wmax.to_uhwi ());
	    }
	  else
	    {
	      gcc_unreachable ();
	    }
	}
    }
  write_char ('_');
  write_type (TREE_TYPE (type));
}

/* Non-terminal <substitution>.

      <substitution> ::= S <seq-id> _
		     ::= S_  */

static void
write_substitution (const int seq_id)
{
  write_char ('S');
  if (seq_id > 0)
    write_number (seq_id - 1, /*unsigned=*/1, 36);
  write_char ('_');
}

/* Start mangling ENTITY.  */

static inline void
start_mangling (void)
{
  obstack_free (&name_obstack, name_base);
  mangle_obstack = &name_obstack;
  name_base = obstack_alloc (&name_obstack, 0);
}

/* Done with mangling.  */

static void
finish_mangling_internal (void)
{
  /* Clear all the substitutions.  */
  vec_safe_truncate (G.substitutions, 0);

  /* Null-terminate the string.  */
  write_char ('\0');
}

/* Like finish_mangling_internal, but return the mangled string.  */

static inline const char *
finish_mangling (void)
{
  finish_mangling_internal ();
  return (const char *) obstack_finish (mangle_obstack);
}

/* Like finish_mangling_internal, but return an identifier.  */

static tree
finish_mangling_get_identifier (void)
{
  finish_mangling_internal ();
  /* Don't obstack_finish here, and the next start_mangling will
     remove the identifier.  */
  return get_identifier ((const char *) obstack_base (mangle_obstack));
}

/* Initialize data structures for mangling.  */

void
init_mangle (void)
{
  gcc_obstack_init (&name_obstack);
  name_base = obstack_alloc (&name_obstack, 0);
  vec_alloc (G.substitutions, 0);
}

/* Generate the mangled name of DECL.  */

static tree
mangle_decl_string (const tree decl)
{
  tree result;

  start_mangling ();

  if (TREE_CODE (decl) == TYPE_DECL)
    write_type (TREE_TYPE (decl));
  else
    write_mangled_name (decl, true);

  result = finish_mangling_get_identifier ();

  return result;
}

/* Return an identifier for the external mangled name of DECL.  */

static tree
get_mangled_id (tree decl)
{
  tree id = mangle_decl_string (decl);
  return targetm.mangle_decl_assembler_name (decl, id);
}

void
mangle_decl (const tree decl)
{
  tree id;

  id = get_mangled_id (decl);

  SET_DECL_ASSEMBLER_NAME (decl, id);
}

/* True iff T is a transaction-safe function type.  */

static bool
tx_safe_fn_type_p (tree t)
{
  if (TREE_CODE (t) != FUNCTION_TYPE)
    return false;
  return !!lookup_attribute ("transaction_safe", TYPE_ATTRIBUTES (t));
}

#include "gt-c-c-mangle.h"
