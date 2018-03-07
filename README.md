
# Not yet implemented

- Standard library
- More eval tests
- Public API for the crate

# Improvements and optimizations

 - Suggestion in identifier not found
 - Error improvements: suggestions, better span
 - Precomputation / cache of static content for function definition
 - Rewrite of += so that we do not recompute index() in a[index()] += 1 (right now <=> a[index()] = a[index()] + 1)
