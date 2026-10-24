Checksum/ adapts generic proof tactics and CRC algebra from the pinned Varnish
esi_parse_fuzzer proof library at upstream commit 98e995d4daced70a0a4aa2c810854b88720735f1.
Original source notices are retained. CrcGenInner.v changes the instruction
layout and register allocation to zlib; CrcLib.v changes the x2n table address.
BWorld.v keeps only the generic budget definitions, omitting unrelated Varnish
instruction certificates. CrcGenModel.v is a new mathematical model; a model
theorem alone does not establish a machine-code or catalog theorem.

Reusable/ contains generic lemmas and candidate binary-specific adaptations
from the pinned cgif proof library. Each completed adaptation is checked against
zlib's own unchanged ELF image; copying and relocation alone establish nothing.
Their original Copyright 2026 Anthropic PBC and Apache-2.0 OR MIT notices are
retained in every source file. ZImage.v adapts its binary setup pattern to the
fixed zlib image. The MIT alternative is used here; the repository's MIT
licence applies to that material.

The instruction-case proof pattern in StartupExit.v is adapted from LinuxProcessSemantics.LinuxProcessSem.Checks.SpuriousCfg.exits_c_must_exit_at_cfg at semantics commit f1006fe8178338a499b5e5c41be83006c4edd058. Its original licence follows.

MIT License

Copyright (c) 2026 Theorem Labs, PBC

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
