# The `endure` Language

## Warning

This is an **experimental** language, and features/goals may change abruptly. **Use this at your own risk**.

## Introduction

Do you want to program at a lower level without dealing with a borrow checker or a garbage collector? If so, this language is for you!

Some of our main features can be found under the `Goals` section.

## Examples

Here are a few examples showcasing what you can currently do with this language:

```endure
# This is a comment
# Let's declare a namespace

#doc This library does x, y, z.
namespace MyLibrary {
    #doc Here we're gonna process some data.
    func processData(data: i64): i64 {
        return data * 2;
    }
}

# Or we can declare something outside
# of a namespace.
#
# Everything declared globally is
# within the `program` namespace.
func squared(i: i64): i64 {
    return i * i;
}

# Our entrypoint
func main() {
    let sixteen := squared(4);

    # Now we need to process the data
    let processed := processData(sixteen);

    return;
}

Here we see the declaration of some more complex data structures:

#doc Someone in this world!
type Person = struct {
    id: u32,
    age: u8,
}

#doc Creates a person.
func createPerson(id: u32, age: u8): Person {
    return Person {
        id,
        age,
    };
}

# You can also define unions!
type Number = union {
    int: i64,
    float: f64,
}

## Goals

The current language goals are:

- [x] Declaration of functions;
- [x] Declaration of namespaces;
- [x] Search of elements within the current namespace;
- [x] Generic functions (templates);
- [x] Union types;
- [x] Pattern matching;
- [ ] Sum types;
- [ ] Comment documentation with `#doc`;
- [ ] Powerful metaprogramming functions;
- [ ] Use of elements from outer namespaces; and
- [ ] Importing namespaces from an include path.

What is urgent right now (will be done before language goals):

- [ ] Generic aggregate data types (and their methods); and
- [ ] A C foreign function interface.
