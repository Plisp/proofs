#!/bin/bash

find . -name '*.mhs' -type f -exec sh -c '
for f; do
    stack exec minhs-2 -- --no-colour --dump type-infer "$f" > "${f%.mhs}.out"
done' - {} +
