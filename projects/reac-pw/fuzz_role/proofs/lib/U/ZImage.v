(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: written for zlib/checksum_fuzzer on the frame of the cgif proof's library; 18 of its 48 lines of code, among them its imports, match lines of proofs/cgif/cgif_rgb_fuzzer/lib/YH05.v up to addresses and numbers, and the rest is new. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the CONFIG_RSEQ flag and the auxv; the launch's ProcInput (kernel build, exec file name, SIGPIPE disposition) and entry; the stack strings at the top of the stack VMA); launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
(** Symbolic initial memory for the fixed checksum_fuzzer plain image. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import
  YK11 YP0m YP09 YP0l YP08 YP02.
From OSSVerify.reac_pw.fuzz_role.images Require Ubsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.

Definition zsegs : list Segment := Ubsan.M.loaded_segments.
Definition ztext_start : Z := 0x128d4.
Definition ztext_count : nat := 10758.
Definition ztbl : ctable := Eval vm_compute in
  (build_table zsegs ztext_start ztext_count TEmpty).
Lemma ztbl_eq : ztbl = build_table zsegs ztext_start ztext_count TEmpty.
Proof. vm_compute. reflexivity. Qed.
Lemma ztbl_ok : table_ok zsegs ztbl.
Proof. rewrite ztbl_eq. apply build_table_ok0. unfold ztext_start. lia. Qed.

Definition zimg : smem :=
  [mkRegion None 0x10000 0x12000 0 0 [mkChunk 0x10000 (CImg 0x2000)];
   mkRegion None 0x12000 0x1e000 0 0 [mkChunk 0x12000 (CImg 0xc000)];
   mkRegion None 0x1e000 0x1f000 0x1e000 0x1f000 [mkChunk 0x1e000 (CImg 0x1000)];
   mkRegion None 0x1f000 0x51000 0x1f000 0x51000 [mkChunk 0x1f000 (CImg 0x32000)]].
Lemma zimg_ok : img_check zsegs zimg = true.
Proof. vm_compute. reflexivity. Qed.
Definition zpc0 : Z := 0x128d4.
Definition zW : Z := 131072.
Definition zss0 (rs two : bool) : sstate := ss0 rs zpc0 Ubsan.M.phdrs zW two zimg.
Lemma z_init_pc_eq : Z.of_N Ubsan.M.init_pc = zpc0.
Proof. reflexivity. Qed.

Theorem z_init_st_ok : forall
  (inp : ProcInput) (mbase sp brk : word) (rnd : EntryDraw)
  (xw : nat -> word) (xd : nat -> list byte) (two : bool),
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
  xd UID_DATOM = uid_bytes (in_uid inp) -> xd HWCAP_DATOM = hwcap_bytes (in_hwcap inp) ->
  xd RAND_DATOM = rand_bytes rnd -> xd GID_DATOM = gid_bytes (in_gid inp) ->
  xd EHDR_DATOM = ehdr_bytes inp sp mbase ->
  xd EXECFN_DATOM = execfn_ptr_bytes (ed_top rnd) (in_execfn inp) ->
  (if two then 2 <= length (in_argv inp) else True)%nat ->
  st_ok zsegs (E0 sp (ed_top rnd) (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp) (in_execfn inp) xw xd)
    (zss0 (kb_rseq (in_kernel inp)) two)
    (init_machine_state zsegs Ubsan.M.init_pc Ubsan.M.phdrs sp mbase rnd inp).
Proof.
  intros inp mbase sp brk rnd xw xd two Hsp Hva Hve Hvl Hlau Hxd Hxh Hxr Hxg Hxe Hxf Htwo.
  unfold zss0. rewrite <- z_init_pc_eq.
  eapply init_st_ok;
    first [ exact Hsp | exact Hva | exact Hve | exact Hvl | exact Hlau
          | exact Hxd | exact Hxh | exact Hxr | exact Hxg | exact Hxe | exact Hxf
          | exact Htwo | exact zimg_ok | (unfold zW; lia) ].
Qed.

Set Printing Fully Qualified.
Print Assumptions z_init_st_ok.
