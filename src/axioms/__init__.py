"""Language-neutral support for DIG's algebraic API axiom analysis."""

from .spec import Manifest, SpecValidationError, load_manifest, validate_manifest

__all__ = ["Manifest", "SpecValidationError", "load_manifest", "validate_manifest"]

