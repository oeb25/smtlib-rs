@_default:
    just --list

# Code generation

# generate the ast and logics
generate:
    cargo xtask ast
    cargo xtask logics

alias gen := generate

# CI/Release

release-patch args="":
    git checkout HEAD -- CHANGELOG.md
    cargo release patch {{args}}

release-hook:
    git cliff -t $NEW_VERSION -o CHANGELOG.md
