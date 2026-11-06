(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb...): the entry addresses of the
   library wrappers that only the interceptor layer's closings name. Each value is the address of the symbol named
   beside it in the unstripped twin's .symtab (fuzz_segconf.asan.debug, sha256 4362701197e4cecd...; LOAD2-4 of pin and
   twin are byte-equal). The entries the frame also names (PC_strlen, PC_strcmp, PC_strncmp, PC_strspn, PC_strtol,
   PC_snprintf, PC_memchr, PC_region_is_poisoned, PC_stack_free_5, A_SSP_GOT, A_SSP_GUARD) are in lib/A/Rt/RtAPI.v, not
   here.
   Statement text only: no function of the binary is proved here. *)
From Stdlib Require Import ZArith.
Local Open Scope Z_scope.

Definition PC_strcasecmp : Z := 0x43a1c.   (* __interceptor_trampoline_strcasecmp, 4 B *)
Definition PC_strncasecmp : Z := 0x43a20.  (* __interceptor_trampoline_strncasecmp, 4 B *)
Definition PC_strstr : Z := 0x43a24.       (* __interceptor_trampoline_strstr, 4 B *)
Definition PC_strchr : Z := 0x43a28.       (* __interceptor_trampoline_strchr, 4 B *)
Definition PC_strrchr : Z := 0x43a2c.      (* __interceptor_trampoline_strrchr, 4 B *)
Definition PC_vsnprintf : Z := 0x43a5c.    (* __interceptor_trampoline_vsnprintf, 4 B *)
Definition PC_strncpy : Z := 0x43ab4.      (* __interceptor_trampoline_strncpy, 4 B *)
Definition PC_calloc : Z := 0x56c38.       (* __interceptor_trampoline_calloc, 4 B *)
Definition PC_isalnum : Z := 0x901a0.      (* isalnum (musl, called directly, not wrapped), 28 B *)
