@_default:
    just --list

# Code generation

# generate the ast and logics
generate:
    cargo xtask ast
    cargo xtask logics

alias gen := generate

# CI/Release

# release crates. specify "patch" or "minor" or "major" to bump the version
release args="patch":
    git checkout HEAD -- CHANGELOG.md
    cargo release {{args}}

# the release hook used by `cargo release`
release-hook:
    git cliff -t $NEW_VERSION -o CHANGELOG.md
