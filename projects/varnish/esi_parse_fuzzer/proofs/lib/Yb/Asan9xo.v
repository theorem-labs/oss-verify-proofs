(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the conversions take the new AsanInit arguments, the main-entry facts read argv's strings and their slack at the top of the launch's block (with the launch premise), the 6144512-byte mapped stack below sp and the launch's argument layout, and the main-entry state checks and entry facts are stated over the hand-off states computed at each value of the run's CONFIG_RSEQ flag ([AsanRegen2]) in the place of the recorded ones. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Instr Sem.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Mem Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanAcct AxSyioe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanz3l AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm Asanjze AsanInit AsanRegen2 Asanii6.

Module Asanycn.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Instr Sem.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanAcct AxSyioe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanz3l AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm Asanjze AsanInit Asanii6.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.AxSyetn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanz3l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.Asanfbz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanjze OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanInit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanii6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Mem.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation Lbytes_at := (Lib.Mem.bytes_at ASEGS).

Section Conv.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  (* LPS 727298f3: AsanInit's [SINV0]/[argH0] read the mmap base, AT_GID, the kernel build
     and the exec file name *)
  Variables mbase gid : word.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  #[local] Notation SINV := (SINV0 ASAN APH sp rdraw brk0 mbase argv envp uid gid hw kb execfn).
  #[local] Notation argH := (argH0 sp rdraw argv envp kb execfn).
  Context {BL : AsanInit.BootLim}.   (* [comment removed for export] *)
  #[local] Notation LIM := (@AsanInit.blim BL).
  Variable cs : acs.
  Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis CS : cs_ok ASEGS ASAN LIM SINV argH fs E cs R FULL model.
  #[local] Notation MB := (mb FULL).
  #[local] Notation KH := (khas cs).

  Lemma length_word_to_le_bytes : forall w v, length (word_to_le_bytes w v) = w.
  Proof. intros. unfold word_to_le_bytes. apply length_Z_to_le_bytes. Qed.

  (* [comment removed for export] *)
  Lemma mrd_mb : forall a, Lib.Mem.mrd ASEGS FULL (Lib.Mem.wa a) = MB a.
  Proof. intros a. reflexivity. Qed.

  Lemma bytes_at_of_mb : forall a bs, 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
    (forall i, (i < length bs)%nat -> MB (a + Z.of_nat i) = nth_error bs i) -> Lbytes_at FULL a bs.
  Proof. intros a bs Ha Hl H. split; [exact Ha|]. split; [exact Hl|]. intros i Hi. rewrite mrd_mb. apply H. exact Hi. Qed.

  (* [comment removed for export] *)
  Lemma cells_bytes : forall l, cells_okb cs l = true -> Forall (fun c => Lbytes_at FULL (fst c) (snd c)) l.
  Proof.
    intros l H. pose proof (cells_okb_sound sp rdraw brk0 argv envp uid hw mbase gid kb execfn fs Hsp Hva cs E R FULL model CS l H) as F.
    apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) F c Hc) as (X1 & X2 & X3).
    apply bytes_at_of_mb; assumption.
  Qed.
  Lemma cells_nth : forall l i a bs, cells_okb cs l = true -> nth_error l i = Some (a, bs) -> Lbytes_at FULL a bs.
  Proof.
    intros l i a bs H Hn. pose proof (proj1 (Forall_forall _ _) (cells_bytes l H) (a, bs) (nth_error_In _ _ Hn)) as X. exact X.
  Qed.

  (* [comment removed for export] *)
  Lemma word_lit_img : forall a w ve, KH (KWord (SA (ELit 0) a) w ve) = true ->
    img_lo ASAN <= a -> a + Z.of_nat w <= img_hi ASAN ->
    Lbytes_at FULL a (word_to_le_bytes w (edenot E ve)).
  Proof.
    intros a w ve H Hlo Hhi. cbn [img_lo img_hi ASAN] in Hlo, Hhi.
    pose proof (pre_word_img_at sp rdraw brk0 argv envp uid hw mbase gid kb execfn fs Hsp Hva cs E R FULL model CS (ELit 0) 0 (ub_lit E) a w ve H
                  ltac:(cbn [img_lo ASAN]; lia) ltac:(cbn [img_hi ASAN]; lia)) as RD.
    rewrite Z.add_0_l in RD.
    apply bytes_at_of_mb; [lia| rewrite length_word_to_le_bytes; lia|].
    intros i Hi. rewrite length_word_to_le_bytes in Hi.
    pose proof (rdn_mbytes FULL w (Z_to_bv 64 a) _ RD i Hi) as X. rewrite u_lit64a, Z.mod_small in X by lia.
    unfold mb. rewrite X. symmetry. apply nth_error_nth'. rewrite length_word_to_le_bytes. exact Hi.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma word_sym : forall b B off w ve, bv_unsigned (edenot E b) = B -> KH (KWord (SA b off) w ve) = true ->
    0 <= B + off -> (B + off + Z.of_nat w <= img_lo ASAN \/ img_hi ASAN <= B + off) -> B + off + Z.of_nat w <= 2^64 ->
    Lbytes_at FULL (B + off) (word_to_le_bytes w (edenot E ve)).
  Proof.
    intros b B off w ve Ub H H0 Hlo Hhi. cbn [img_lo img_hi ASAN] in Hlo.
    assert (ROM : forall j, (j < w)%nat -> seg_rom ASEGS (Z_to_bv 64 (B + off + Z.of_nat j)) = None).
    { intros j Hj. unfold seg_rom, memory_read. rewrite u_lit64a, Z.mod_small by lia.
      rewrite (find_segment1_none_outside ASEGS (img_lo ASAN) (img_hi ASAN)); [reflexivity| exact asan_segs_in_hull| cbn [img_lo img_hi ASAN]; lia]. }
    pose proof (pre_word_at sp rdraw brk0 argv envp uid hw mbase gid kb execfn fs cs E R FULL model CS b B Ub off w ve H ltac:(lia) Hhi ROM) as X.
    apply bytes_at_of_mb; [lia| rewrite length_word_to_le_bytes; lia|].
    intros i Hi. rewrite length_word_to_le_bytes in Hi. unfold mb. rewrite (X i Hi). symmetry. apply nth_error_nth'. rewrite length_word_to_le_bytes. exact Hi.
  Qed.

  (* [comment removed for export] *)
  Lemma zero_sym : forall b B off n, bv_unsigned (edenot E b) = B -> KH (KZero (SA b off) (ELit n)) = true -> 0 <= n < 2^64 ->
    forall i, 0 <= i < n -> FULL (Z_to_bv 64 (B + off + i)) = Some (Z_to_bv 8 0).
  Proof. intros b B off n Ub H Hn. exact (pre_zero_at sp rdraw brk0 argv envp uid hw mbase gid kb execfn fs cs E R FULL model CS b B Ub off n H Hn). Qed.

  Lemma fill_bytes : forall a n c, 0 <= a -> 0 <= n -> a + n <= 2^64 ->
    (forall i, 0 <= i < n -> FULL (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 c)) ->
    Lbytes_at FULL a (repeat (Z_to_bv 8 c) (Z.to_nat n)).
  Proof.
    intros a n c Ha Hn Hhi H. apply bytes_at_of_mb; [lia| rewrite repeat_length; lia|].
    intros i Hi. rewrite repeat_length in Hi. unfold mb. rewrite (H (Z.of_nat i)) by lia.
    symmetry. rewrite nth_error_repeat; [reflexivity| exact Hi].
  Qed.

  (* [comment removed for export] *)
  Lemma mapped_sym : forall b B off n, bv_unsigned (edenot E b) = B -> KH (KWr (SA b off) (ELit n)) = true ->
    0 <= B + off -> (B + off + n <= img_lo ASAN \/ img_hi ASAN <= B + off) -> 0 <= n < 2^64 -> B + off + n <= 2^64 ->
    forall i, 0 <= i < n -> FULL (Z_to_bv 64 (B + off + i)) <> None.
  Proof.
    intros b B off n Ub H H0 Hlo Hn Hhi. cbn [img_lo img_hi ASAN] in Hlo.
    apply (pre_wr_at sp rdraw brk0 argv envp uid hw mbase gid kb execfn fs cs E R FULL model CS b B Ub off n H ltac:(lia) Hn Hhi).
    intros i Hi. apply (find_segment1_none_outside ASEGS (img_lo ASAN) (img_hi ASAN)); [exact asan_segs_in_hull| cbn [img_lo img_hi ASAN]; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma img_zero_fill : forall lo' hi' lo n, KH (KImg lo' hi') = true -> lo' <= lo -> lo + n <= hi' -> 0 <= n ->
    img_lo ASAN <= lo' -> hi' <= img_hi ASAN ->
    (forall a, lo <= a < lo + n -> seg_rom ASEGS (Z_to_bv 64 a) = Some (Z_to_bv 8 0)) ->
    Lbytes_at FULL lo (repeat (Z_to_bv 8 0) (Z.to_nat n)).
  Proof.
    intros lo' hi' lo n KI H1 H2 Hn Hlo Hhi HZ. cbn [img_lo img_hi ASAN] in Hlo, Hhi.
    apply bytes_at_of_mb; [lia| rewrite repeat_length; lia|].
    intros i Hi. rewrite repeat_length in Hi.
    destruct (kimg_zero_range sp rdraw brk0 argv envp uid hw mbase gid kb execfn fs Hsp Hva cs E R FULL model CS lo' hi' lo (lo + n) KI H1 H2
                ltac:(cbn [img_lo ASAN]; lia) ltac:(cbn [img_hi ASAN]; lia) HZ (lo + Z.of_nat i) ltac:(lia)) as [_ X].
    rewrite X. symmetry. rewrite nth_error_repeat; [reflexivity| exact Hi].
  Qed.
End Conv.
End Asanycn.


Module Asannjs.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec AxSyioe Asanz3l AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm Asanjze AsanInit AsanRegen2 Asanii6.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanz3l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.Asanfbz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanjze OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanInit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanRegen2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanii6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require DA_Entry.
Import ListNotations. Import AX2. Import APC. Import AP. Import APS.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition e_pgsh : expr := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 512) (EVar 10)).
Definition e_shlen : expr :=
  EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-512)) (EVar 10))) (ELit 17592187092992).
(* LPS 727298f3: the slack after argv[0]/argv[1] is read from the strings area at the top of
   the launch's block, no longer from the sixteen AT_RANDOM bytes, so the old AT_RANDOM blob
   key and its [usp + 8*argc + 8*envc + 8*W]-based address are gone. *)

(* [comment removed for export] *)
Definition entry_keys : list kentry :=
  [ KWr (SA (ELit 0) 0xa8000) (ELit 0x562000);
    KWord (SA (ELit 0) 0x5e8330) 4%nat (EVar 44);
    KRange (EVar 44) 1 4194303;
    KImg 65536 0xab078;
    KZero (SA e_pgsh 2146402304) e_shlen;
    KRange (EVar 10) 0 7 ].
Definition chk_entry (cs : acs) : bool := forallb (fun K => existsb (kentry_eqb K) (kn cs)) entry_keys.
(* LPS 727298f3: the main-entry hand-off states are the ones [AsanRegen2] computes at each value
   [r] of the run's CONFIG_RSEQ flag; each check is computed at both values.
   The computed states carry [entry_keys] and the [DA_Entry.MAIN_CELLS] cells at the recorded
   states' variable numbers (the thread id at [EVar 44], [EVar 0]/[EVar 10] in the shadow keys),
   because [AsanRegen] renames the root hand-off states' fresh variables back to the recorded
   numbers; the vm decides each check at Qed on the computed states. *)
Lemma chk_entry_1 : forall r, 0 <= r <= 1 -> chk_entry (HS_asan2_1r r) = true.
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; vm_compute; reflexivity. Qed.
Lemma chk_entry_2 : forall r, 0 <= r <= 1 -> chk_entry (HS_asan2_2r r) = true.
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; vm_compute; reflexivity. Qed.
Lemma chk_entry_3 : forall r, 0 <= r <= 1 -> chk_entry (HS_asan2b_1r r) = true.
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; vm_compute; reflexivity. Qed.
Lemma chk_entry_4 : forall r, 0 <= r <= 1 -> chk_entry (HS_asan2b_2r r) = true.
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; vm_compute; reflexivity. Qed.
Lemma main_cells_1 : forall r, 0 <= r <= 1 -> cells_okb (HS_asan2_1r r) DA_Entry.MAIN_CELLS = true.
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; vm_compute; reflexivity. Qed.
Lemma main_cells_2 : forall r, 0 <= r <= 1 -> cells_okb (HS_asan2_2r r) DA_Entry.MAIN_CELLS = true.
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; vm_compute; reflexivity. Qed.
Lemma main_cells_3 : forall r, 0 <= r <= 1 -> cells_okb (HS_asan2b_1r r) DA_Entry.MAIN_CELLS = true.
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; vm_compute; reflexivity. Qed.
Lemma main_cells_4 : forall r, 0 <= r <= 1 -> cells_okb (HS_asan2b_2r r) DA_Entry.MAIN_CELLS = true.
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; vm_compute; reflexivity. Qed.
End Asannjs.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.FileSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.AxSyetn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanz3l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.Asanfbz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanjze OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanInit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanRegen2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanii6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asan9xo.Asanycn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asan9xo.Asannjs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require DA_Eg3i DA_Cells DA_Entry.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation Lbytes_at := (Mem.bytes_at ASEGS).

Section Entry.
  Context {Clg : Ceiling.Ceiling}.   (* [comment removed for export] *)
  Variable sp : word.
  Hypothesis HCEIL : Ceiling.alloc_ceiling = bv_unsigned sp - 0x800000.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  (* LPS 727298f3: as [Asanii6.Extract] *)
  Variables mbase gid : word.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  (* LPS 727298f3: [Run.valid_entry]'s fifth conjunct, over the stack's view of the input:
     it bounds the block by the stack VMA's end, so argv's strings lie below 2^47 *)
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) (AsanInit.stk_inp argv envp uid gid hw kb execfn).
  #[local] Notation SINV := (SINV0 ASAN APH sp rdraw brk0 mbase argv envp uid gid hw kb execfn).
  #[local] Notation argH := (argH0 sp rdraw argv envp kb execfn).
  Context {BL : AsanInit.BootLim}.   (* [comment removed for export] *)
  #[local] Notation LIM := (@AsanInit.blim BL).
  Variable cs : acs.
  Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis CS : cs_ok ASEGS ASAN LIM SINV argH fs E cs R FULL model.
  Hypothesis CHK : chk_all (rseq_z (kb_rseq kb)) cs = true.
  Hypothesis CHKE : chk_entry cs = true.
  Hypothesis CC : cells_okb cs DA_Entry.MAIN_CELLS = true.
  #[local] Notation usp := (bv_unsigned sp).
  #[local] Notation inp0 := (AsanInit.stk_inp argv envp uid gid hw kb execfn).
  #[local] Notation bsb := (entry_stack_image inp0 mbase APH (Z_to_bv 64 (a_entry ASAN)) sp rdraw).
  (* argv[0]'s first byte: sp + C + W ([AsanInit]'s STR0) *)
  #[local] Notation STR0 := (usp + Z.of_nat (block_head_size (kb_rseq kb) argv envp)
                              + Z.of_nat (block_pad_len (kb_rseq kb) sp (ed_top rdraw) argv envp execfn)).
  (* the launch's argument layout, as [DA_Entry] reads it *)
  #[local] Notation LAYa := (DA_Entry.launch_lay sp (ed_top rdraw) (kb_rseq kb) argv envp execfn).

  Let MP : main_pre sp rdraw brk0 argv envp uid hw mbase gid kb execfn fs R FULL model :=
    main_pre_of_cs_ok sp rdraw brk0 argv envp uid hw mbase gid kb execfn fs Hsp Hva Hve Hfit Hlau cs E R FULL model CHK CS.

  (* [comment removed for export] *)
  Lemma khas_entry : forall K, In K entry_keys -> khas cs K = true.
  Proof.
    intros K HK. unfold chk_entry in CHKE. apply forallb_forall with (x := K) in CHKE; [exact CHKE| exact HK].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma usp_facts : sp_window_lo <= usp /\ usp + entry_stack_span argv envp <= 2^47 /\ usp mod 16 = 0.
  Proof.
    pose proof Hsp as (H1 & H2 & H3). unfold entry_stack_fits, sp_window_hi in Hfit. unfold sp_window_lo in *.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia.
  Qed.

  Lemma argc_ge1 : (1 <= length argv)%nat.
  Proof. pose proof Hva as [H _]. lia. Qed.

  Lemma tab_cons : forall a l, total_arg_bytes (a :: l) = Z.of_nat (length a) + 1 + total_arg_bytes l.
  Proof. intros a l. rewrite !total_arg_bytes_Z. cbn [total_arg_bytes_nat fold_right]. fold (total_arg_bytes_nat l). lia. Qed.
  Lemma tab_nonneg : forall l, 0 <= total_arg_bytes l.
  Proof. intros l. rewrite total_arg_bytes_Z. lia. Qed.
  Lemma tab_ge1 : forall l : list (list byte), (1 <= length l)%nat -> Z.of_nat (length (nth 0 l [])) + 1 <= total_arg_bytes l.
  Proof. intros [|a l] H; [cbn in H; lia|]. cbn [nth]. rewrite tab_cons. pose proof (tab_nonneg l). lia. Qed.
  Lemma tab_ge2 : forall l : list (list byte), (2 <= length l)%nat ->
    Z.of_nat (length (nth 0 l [])) + 1 + Z.of_nat (length (nth 1 l [])) + 1 <= total_arg_bytes l.
  Proof.
    intros [|a [|b l]] H; try (cbn in H; lia). cbn [nth]. rewrite !tab_cons. pose proof (tab_nonneg l). lia.
  Qed.
  Lemma tab_firstn_gen : forall (l : list (list byte)) k, (k < length l)%nat ->
    total_arg_bytes (firstn k l) + Z.of_nat (length (nth k l [])) + 1 <= total_arg_bytes l.
  Proof.
    induction l as [|a l IH]; intros k Hk; [cbn in Hk; lia|].
    destruct k as [|k]; [cbn [firstn nth]; rewrite tab_cons; change (total_arg_bytes []) with 0; pose proof (tab_nonneg l); lia|].
    cbn [firstn nth]. rewrite !tab_cons. specialize (IH k ltac:(cbn in Hk; lia)). lia.
  Qed.
  Lemma tab_firstn1 : forall l : list (list byte), (2 <= length l)%nat -> total_arg_bytes (firstn 1 l) = Z.of_nat (length (nth 0 l [])) + 1.
  Proof.
    intros [|a l] H; [cbn in H; lia|]. cbn [firstn nth]. rewrite tab_cons.
    change (firstn 0 l) with (@nil (list byte)). change (total_arg_bytes []) with 0. lia.
  Qed.

  (* LPS 727298f3: THE BLOCK AT THE REVISION.  The launch puts argv's strings, then envp's,
     the exec file name with its NUL and the eight-byte slot at the TOP of the block, above
     the AT_RANDOM bytes and the [arch_align_stack] pad ([StackLayout.build_stack_bytes]);
     [Asanii6.lau_block] reads the end and the unclamped pad off [Hlau]. *)
  Lemma lau_facts : bv_unsigned (ed_top rdraw) <= 2 ^ 47
    /\ STR0 + Z.of_nat (launch_string_bytes argv envp execfn) + 8 = bv_unsigned (ed_top rdraw).
  Proof. pose proof (lau_block sp brk0 mbase rdraw argv envp uid gid hw kb execfn Hlau) as (L1 & L2 & _). split; lia. Qed.

  Lemma lstr_eq : Z.of_nat (launch_string_bytes argv envp execfn)
    = total_arg_bytes argv + total_arg_bytes envp + Z.of_nat (length execfn) + 1.
  Proof. unfold launch_string_bytes. rewrite !length_flatten_strings, !total_arg_bytes_Z. lia. Qed.

  (* [DA_Entry]'s argv[0] under the launch's layout is [Asanii6.p0a] *)
  Lemma P0E : DA_Entry.e_p0a (LAY:=LAYa) usp argv envp = Asanii6.p0a sp rdraw argv envp kb execfn.
  Proof.
    unfold DA_Entry.e_p0a, DA_Entry.e_argc, DA_Entry.e_envc, DA_Entry.launch_lay, Asanii6.p0a, Asanii6.usp. cbn [DA_Entry.al_pad].
    assert (HB : (8 * length argv + 8 * length envp + 184 <= block_head_size (kb_rseq kb) argv envp)%nat).
    { generalize (kb_rseq kb) as b. intros b. unfold block_head_size, block_items, auxv_size, auxv_count. cbv zeta.
      generalize ((length argv + length envp + 3) mod 2)%nat as q. intros q. destruct b; cbv beta iota; lia. }
    lia.
  Qed.
  Lemma SPN : DA_Entry.e_span (LAY:=LAYa) argv envp = Asanii6.p0a sp rdraw argv envp kb execfn - usp + total_arg_bytes argv + 8.
  Proof. rewrite <- P0E. unfold DA_Entry.e_span, DA_Entry.e_p0a. lia. Qed.
  Lemma TOPS : Asanii6.p0a sp rdraw argv envp kb execfn + total_arg_bytes argv + total_arg_bytes envp + Z.of_nat (length execfn) + 9
    = bv_unsigned (ed_top rdraw).
  Proof. pose proof lau_facts as (_ & T2). pose proof lstr_eq. unfold Asanii6.p0a, Asanii6.usp. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma bytes_at_pointwise : forall a bs, 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
    (forall j, (j < length bs)%nat -> FULL (Z_to_bv 64 (a + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0))) ->
    Lbytes_at FULL a bs.
  Proof.
    intros a bs Ha Hl H. apply (bytes_at_of_mb FULL a bs Ha Hl). intros i Hi. unfold mb.
    rewrite (H i Hi). symmetry. apply nth_error_nth'. exact Hi.
  Qed.

  (* [comment removed for export] *)
  Lemma wview_Mr_FULL : forall a, wview ASEGS (Mr ASAN argH E cs model FULL) a <> None -> wview ASEGS FULL a <> None.
  Proof.
    intros a H. unfold wview in *. unfold Mr, mrestrict in H.
    destruct (hid ASAN argH E cs model a); destruct (FULL a); try exact H; discriminate.
  Qed.

  (* LPS 727298f3: any piece of the strings area [STR0, ed_top) of the block is in memory as
     the block lays it: [argH0] hides that area and [SINV0] pins it to the launch image. *)
  Lemma block_bytes : forall pre mid post, bsb = pre ++ mid ++ post ->
    STR0 <= usp + Z.of_nat (length pre) ->
    usp + Z.of_nat (length pre) + Z.of_nat (length mid) <= bv_unsigned (ed_top rdraw) ->
    Lbytes_at FULL (usp + Z.of_nat (length pre)) mid.
  Proof.
    intros pre mid post EI L1 L2.
    pose proof lau_facts as (T1 & T2).
    pose proof usp_facts as (U1 & U2 & U3). unfold sp_window_lo in U1.
    pose proof (Nat2Z.is_nonneg (length pre)).
    assert (NW : usp + Z.of_nat (length bsb) < 2 ^ 64).
    { rewrite (length_entry_stack_image_launch Sv48 inp0 mbase APH (Z_to_bv 64 (a_entry ASAN)) sp brk0 rdraw Hlau). lia. }
    pose proof (read_at_offset_image ASEGS inp0 mbase APH (Z_to_bv 64 (a_entry ASAN)) sp rdraw pre mid post (length mid) EI eq_refl NW) as RS.
    rewrite word_add_nat_Z2bv in RS.
    set (a0 := usp + Z.of_nat (length pre)) in *.
    assert (RD : rdn ASEGS FULL (Z_to_bv 64 a0) (length mid) = Some mid).
    { rewrite (rdn_ext FULL (wrap_mem inp0 mbase APH (Z_to_bv 64 (a_entry ASAN)) sp rdraw)).
      - rewrite (rdn_wrap_stack_above ASEGS inp0 mbase APH (Z_to_bv 64 (a_entry ASAN)) sp rdraw (Z_to_bv 64 a0) (length mid))
          by (rewrite u_lit64a, Z.mod_small; lia).
        exact RS.
      - intros j Hj. rewrite u_lit64a, Z.mod_small by lia.
        apply (proj2 (pre_sinv sp rdraw brk0 argv envp uid hw mbase gid kb execfn fs cs E R FULL model CS)).
        unfold argH0. cbv zeta. rewrite u_lit64a, Z.mod_small by lia.   (* [argH0]'s string range is [STR0, ed_top) after zeta *)
        apply orb_true_iff. right. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
    assert (SEG : forall i, (i < length mid)%nat -> seg_rom ASEGS (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a0) + Z.of_nat i)) = None).
    { intros i Hi. apply (seg_rom_off_hull ASEGS ASAN asan_in_hull). unfold in_hull.
      rewrite u_lit64a, Z.mod_small, u_lit64a, Z.mod_small by (rewrite ?u_lit64a, ?Z.mod_small; lia).
      cbn [img_lo img_hi ASAN]. apply andb_false_iff. right. apply Z.ltb_ge. lia. }
    apply bytes_at_pointwise; [lia| lia|].
    intros j Hj. pose proof (rdn_bytes FULL (length mid) (Z_to_bv 64 a0) _ SEG RD j Hj) as X.
    rewrite u_lit64a, Z.mod_small in X by lia. exact X.
  Qed.

  (* LPS 727298f3: argv[k] with its NUL at [STR0 + tab(argv[..k])], and eight more bytes of the
     block after it (the later strings, the exec file name's NUL and the eight-byte slot are
     above it).  It WAS read at [usp + 8*argc + 8*envc + 184 + ...], with sixteen bytes of
     slack reaching into the AT_RANDOM bytes. *)
  Lemma str_k : forall k, (k < length argv)%nat ->
    Lbytes_at FULL (STR0 + total_arg_bytes (firstn k argv)) (nth k argv [] ++ [Z_to_bv 8 0])
    /\ exists sl, length sl = 8%nat
       /\ Lbytes_at FULL (STR0 + total_arg_bytes (firstn k argv) + Z.of_nat (length (nth k argv [])) + 1) sl.
  Proof.
    intros k Hk.
    pose proof lau_facts as (T1 & T2). pose proof lstr_eq as LS.
    pose proof (tab_firstn_gen argv k Hk) as TF. pose proof (tab_nonneg envp) as TE. pose proof (tab_nonneg (firstn k argv)) as TK.
    pose proof (length_entry_stack_image_launch Sv48 inp0 mbase APH (Z_to_bv 64 (a_entry ASAN)) sp brk0 rdraw Hlau) as LI.
    destruct (bsb_byte_k inp0 mbase APH (Z_to_bv 64 (a_entry ASAN)) sp rdraw k Hk) as (pre & post & EI & LP).
    assert (EI2 : bsb = pre ++ (nth k argv [] ++ [Z_to_bv 8 0]) ++ post) by exact EI.
    assert (LP2 : length pre = (block_head_size (kb_rseq kb) argv envp
                                + block_pad_len (kb_rseq kb) sp (ed_top rdraw) argv envp execfn
                                + total_arg_bytes_nat (firstn k argv))%nat) by exact LP.   (* [cat_string_off] and the [stk_inp] projections, by conversion *)
    clear EI LP.
    assert (PRE : usp + Z.of_nat (length pre) = STR0 + total_arg_bytes (firstn k argv)).
    { rewrite LP2, !Nat2Z.inj_add, total_arg_bytes_Z. lia. }
    assert (LEN : Z.of_nat (length bsb) = Z.of_nat (length pre) + Z.of_nat (length (nth k argv [])) + 1 + Z.of_nat (length post)).
    { rewrite EI2, !length_app. cbn [length]. lia. }
    split.
    - rewrite <- PRE. apply (block_bytes pre _ post EI2); [lia|]. rewrite length_app. cbn [length]. lia.
    - assert (PL : (8 <= length post)%nat) by lia.
      exists (firstn 8 post). split; [rewrite firstn_length_le by exact PL; reflexivity|].
      assert (EI3 : bsb = (pre ++ (nth k argv [] ++ [Z_to_bv 8 0])) ++ firstn 8 post ++ skipn 8 post).
      { rewrite EI2, firstn_skipn. apply app_assoc. }
      replace (STR0 + total_arg_bytes (firstn k argv) + Z.of_nat (length (nth k argv [])) + 1)
        with (usp + Z.of_nat (length (pre ++ (nth k argv [] ++ [Z_to_bv 8 0])))) by (rewrite !length_app; cbn [length]; lia).
      apply (block_bytes _ _ _ EI3); rewrite ?length_app, ?firstn_length_le by exact PL; cbn [length]; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* LPS 727298f3: [DA_Entry.entry_raw] under the launch's argument layout [LAYa] *)
  Theorem entry_raw_of_cs : DA_Entry.entry_raw (LAY:=LAYa) usp argv envp fs R FULL model.
  Proof.
    pose proof MP as MP'.
    destruct MP' as [Mra Msp Mgp Mtp Ma0 Ma1 Mhalt Mfs Mfds Mlim Mtid Margb Mp0 Mp1 Mstk Mnone Mwords Mext Mzero Mfill].
    pose proof usp_facts as (U1 & U2 & U3). pose proof lau_facts as (T1 & T2). pose proof TOPS as TP.
    pose proof P0E as PE. pose proof SPN as SN.
    pose proof (tab_nonneg argv) as TA. pose proof (tab_nonneg envp) as TE. pose proof (tab_ge1 argv argc_ge1) as G1.
    assert (U0 : bv_unsigned (edenot E (ELit 0)) = 0) by (cbn [edenot]; rewrite u_lit64a; reflexivity).
    assert (AR : 1 <= Z.of_nat (length argv) <= 1024) by (pose proof Hva as [H _]; exact H).
    assert (ER : 0 <= Z.of_nat (length envp) <= 256) by (pose proof Hve as [H _]; lia).
    assert (CH : usp + 480 <= Asanii6.p0a sp rdraw argv envp kb execfn).
    { unfold Asanii6.p0a, Asanii6.usp. generalize (kb_rseq kb) as b. intros b.
      unfold block_head_size, block_items, auxv_size, auxv_count. cbv zeta.
      generalize ((length argv + length envp + 3) mod 2)%nat as q. intros q. destruct b; cbv beta iota; lia. }
    unfold sp_window_lo in U1.
    constructor.
    - exact Mra.
    - exact Msp.
    - exact Mgp.
    - exact Mtp.
    - exact Ma0.
    - exact Ma1.
    - (* LPS 727298f3: sp to eight bytes past argv's strings, below the stack VMA's end *)
      rewrite SN. unfold sp_window_lo. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
    - rewrite PE, SN. unfold DA_Entry.e_L0. lia.
    - unfold DA_Entry.e_p1a, DA_Entry.e_argc. intros H2. rewrite PE, SN. unfold DA_Entry.e_L0, DA_Entry.e_L1.
      pose proof (tab_ge2 argv ltac:(lia)). lia.
    - exact Mhalt.
    - exact Mfs.
    - exact Mfds.
    - (* [comment removed for export] *)
      exists (bv_unsigned (ev E 44%nat)).
      pose proof (pre_range sp rdraw brk0 argv envp uid hw mbase gid kb execfn fs cs E R FULL model CS 44%nat 1 4194303
                    (khas_entry (KRange (EVar 44%nat) 1 4194303) ltac:(cbn; tauto))) as TR.
      split; [lia|].
      pose proof (word_lit_img sp rdraw brk0 argv envp uid hw mbase gid kb execfn fs Hsp Hva cs E R FULL model CS 0x5e8330 4%nat (EVar 44%nat)
                    (khas_entry (KWord (SA (ELit 0) 0x5e8330) 4%nat (EVar 44%nat)) ltac:(cbn; tauto)) ltac:(cbn; lia) ltac:(cbn; lia)) as TW.
      unfold Mem.le4. rewrite u_lit64a, Z.mod_small by lia. exact TW.
    - (* [comment removed for export] *)
      exact (cells_bytes sp rdraw brk0 argv envp uid hw mbase gid kb execfn fs Hsp Hva cs E R FULL model CS _ CC).
    - (* [comment removed for export] *)
      intros a Ha.
      pose proof (khas_ok sp rdraw brk0 argv envp uid hw mbase gid kb execfn fs cs E R FULL model CS _ (khas_entry (KWr (SA (ELit 0) 0xa8000) (ELit 0x562000)) ltac:(cbn; tauto))) as KW.
      destruct KW as [_ KW].
      rewrite (estart_at E (ELit 0) 0 U0), (elenZ_lit E) in KW by lia.
      specialize (KW (a - 0xa8000) 1%nat ltac:(lia) ltac:(cbn; lia)).
      replace (0 + 688128 + (a - 688128)) with a in KW by lia.
      apply wview_Mr_FULL. cbn [store_ok] in KW.
      destruct (wview ASEGS (Mr ASAN argH E cs model FULL) (Z_to_bv 64 a)); [discriminate| discriminate].
    - (* [comment removed for export] *)
      intros a Ha. apply (Mnone 65536 0xab078 a); [unfold IMG_NONE; left; reflexivity| lia].
    - (* LPS 727298f3: the 6144512 bytes below sp *)
      intros a Ha. unfold DA_Entry.STK_LO in Ha.
      replace a with (Asanii6.usp sp - 6144512 + (a - (usp - 6144512))) by (unfold Asanii6.usp; lia).
      apply Mstk. lia.
    - (* [comment removed for export] *)
      intros a Ha. unfold DA_Entry.STKSH_LO, DA_Entry.STKSH_HI, AIface.sh, kShadowOffset in Ha. rewrite HCEIL in Ha.
      pose proof (khas_ok sp rdraw brk0 argv envp uid hw mbase gid kb execfn fs cs E R FULL model CS _ (khas_entry (KZero (SA e_pgsh 2146402304) e_shlen) ltac:(cbn; tauto))) as KZ.
      cbn [kentry_ok] in KZ. destruct KZ as [_ KZ]. unfold elenZ, estart in KZ. cbn [a_base a_off] in KZ.
      pose proof (pre_v0 sp rdraw brk0 argv envp uid hw mbase gid kb execfn fs cs E R FULL model CS) as V0.
      assert (V10 : bv_unsigned (ev E 10%nat) = (usp mod 32768) / 4096).
      { rewrite (pre_ev_lt9 sp rdraw brk0 argv envp uid hw mbase gid kb execfn fs cs E R FULL model CS 10%nat) by (unfold NX0; lia). unfold E0. cbn [ev vals0 nth].
        rewrite u_lit64a. apply Z.mod_small. Z.div_mod_to_equations. lia. }
      assert (PG : bv_unsigned (edenot E e_pgsh) = 4096 * (usp / 32768) + 512 * ((usp mod 32768) / 4096)).
      { unfold e_pgsh. cbn [edenot]. rewrite !u_add64, !u_mul64_boot, !u_lit64a. rewrite V0, V10. Z.div_mod_to_equations. lia. }
      assert (LN : bv_unsigned (edenot E e_shlen) = 17592187092992 - (4096 * (usp / 32768) + 512 * ((usp mod 32768) / 4096))).
      { unfold e_shlen. cbn [edenot]. rewrite !u_add64, !u_mul64_boot, !u_lit64a. rewrite V0, V10. Z.div_mod_to_equations. lia. }
      rewrite PG, LN in KZ.
      specialize (KZ (a - (4096 * (usp / 32768) + 512 * (usp mod 32768 / 4096) + 2146402304)) ltac:(Z.div_mod_to_equations; lia)).
      match type of KZ with ?M (Z_to_bv 64 ?x) = _ => replace x with a in KZ by lia end.
      exact (Mr_some sp rdraw argv envp kb execfn cs E FULL model _ _ KZ).
    - (* LPS 727298f3: argv[0]'s pointer is [Asanii6.p0a] *)
      rewrite PE. apply bytes_at_pointwise; rewrite ?Mem.length_le8; [lia| cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
      intros j Hj. exact (Mp0 j Hj).
    - (* [comment removed for export] *)
      intros H2. unfold DA_Entry.e_p1a. rewrite PE.
      apply bytes_at_pointwise; rewrite ?Mem.length_le8; [lia| cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
      intros j Hj. exact (Mp1 H2 j Hj).
    - (* LPS 727298f3: argv[0]'s bytes at the top of the block *)
      destruct (str_k 0%nat ltac:(lia)) as [X _]. cbn [firstn] in X.
      replace (total_arg_bytes []) with 0 in X by reflexivity.
      rewrite PE. rewrite Z.add_0_r in X. exact X.
    - (* [comment removed for export] *)
      intros H2. unfold DA_Entry.e_argc in H2.
      destruct (str_k 1%nat ltac:(lia)) as [X _].
      rewrite (tab_firstn1 argv ltac:(lia)) in X.
      unfold DA_Entry.e_p1a. rewrite PE. unfold DA_Entry.e_L0.
      match goal with |- Mem.bytes_at _ _ ?a _ => match type of X with Mem.bytes_at _ _ ?b _ =>
        replace a with b by (unfold Asanii6.p0a, Asanii6.usp; lia) end end. exact X.
    - (* LPS 727298f3: eight bytes of the block after argv[0]'s NUL *)
      destruct (str_k 0%nat ltac:(lia)) as [_ (sl & L & B)]. exists sl. split; [exact L|].
      cbn [firstn] in B. replace (total_arg_bytes []) with 0 in B by reflexivity.
      rewrite PE. unfold DA_Entry.e_L0.
      rewrite Z.add_0_r in B. exact B.
    - (* [comment removed for export] *)
      intros H2. unfold DA_Entry.e_argc in H2.
      destruct (str_k 1%nat ltac:(lia)) as [_ (sl & L & B)]. exists sl. split; [exact L|].
      rewrite (tab_firstn1 argv ltac:(lia)) in B.
      unfold DA_Entry.e_p1a. rewrite PE. unfold DA_Entry.e_L0, DA_Entry.e_L1.
      match goal with |- Mem.bytes_at _ _ ?a _ => match type of B with Mem.bytes_at _ _ ?b _ =>
        replace a with b by (unfold Asanii6.p0a, Asanii6.usp; lia) end end. exact B.
  Qed.
End Entry.

(* [comment removed for export] *)
Section Inst.
  Context {Clg : Ceiling.Ceiling}.
  Variable sp : word.
  Hypothesis HCEIL : Ceiling.alloc_ceiling = bv_unsigned sp - 0x800000.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  Variables mbase gid : word.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) (AsanInit.stk_inp argv envp uid gid hw kb execfn).
  Context {BL : AsanInit.BootLim}.   (* [comment removed for export] *)
  #[local] Notation CSOK HS E R FULL model :=
    (cs_ok ASEGS ASAN (@AsanInit.blim BL) (SINV0 ASAN APH sp rdraw brk0 mbase argv envp uid gid hw kb execfn)
           (argH0 sp rdraw argv envp kb execfn) fs E HS R FULL model).
  #[local] Notation LAYa := (DA_Entry.launch_lay sp (ed_top rdraw) (kb_rseq kb) argv envp execfn).
  (* LPS 727298f3: the run's CONFIG_RSEQ flag as the plan's 0 or 1; the main-entry states are
     [AsanRegen2]'s at it *)
  #[local] Notation RZ := (rseq_z (kb_rseq kb)).

  Theorem entry_raw_1 : forall E R FULL model, CSOK (HS_asan2_1r RZ) E R FULL model -> DA_Entry.entry_raw (LAY:=LAYa) (bv_unsigned sp) argv envp fs R FULL model.
  Proof. intros E R FULL model HC. exact (entry_raw_of_cs sp HCEIL rdraw brk0 argv envp uid hw mbase gid kb execfn fs Hsp Hva Hve Hfit Hlau (HS_asan2_1r RZ) E R FULL model HC
                                            (chk_all_1 RZ (rseq_z_range _)) (chk_entry_1 RZ (rseq_z_range _)) (main_cells_1 RZ (rseq_z_range _))). Qed.
  Theorem entry_raw_2 : forall E R FULL model, CSOK (HS_asan2_2r RZ) E R FULL model -> DA_Entry.entry_raw (LAY:=LAYa) (bv_unsigned sp) argv envp fs R FULL model.
  Proof. intros E R FULL model HC. exact (entry_raw_of_cs sp HCEIL rdraw brk0 argv envp uid hw mbase gid kb execfn fs Hsp Hva Hve Hfit Hlau (HS_asan2_2r RZ) E R FULL model HC
                                            (chk_all_2 RZ (rseq_z_range _)) (chk_entry_2 RZ (rseq_z_range _)) (main_cells_2 RZ (rseq_z_range _))). Qed.
  Theorem entry_raw_3 : forall E R FULL model, CSOK (HS_asan2b_1r RZ) E R FULL model -> DA_Entry.entry_raw (LAY:=LAYa) (bv_unsigned sp) argv envp fs R FULL model.
  Proof. intros E R FULL model HC. exact (entry_raw_of_cs sp HCEIL rdraw brk0 argv envp uid hw mbase gid kb execfn fs Hsp Hva Hve Hfit Hlau (HS_asan2b_1r RZ) E R FULL model HC
                                            (chk_all_3 RZ (rseq_z_range _)) (chk_entry_3 RZ (rseq_z_range _)) (main_cells_3 RZ (rseq_z_range _))). Qed.
  Theorem entry_raw_4 : forall E R FULL model, CSOK (HS_asan2b_2r RZ) E R FULL model -> DA_Entry.entry_raw (LAY:=LAYa) (bv_unsigned sp) argv envp fs R FULL model.
  Proof. intros E R FULL model HC. exact (entry_raw_of_cs sp HCEIL rdraw brk0 argv envp uid hw mbase gid kb execfn fs Hsp Hva Hve Hfit Hlau (HS_asan2b_2r RZ) E R FULL model HC
                                            (chk_all_4 RZ (rseq_z_range _)) (chk_entry_4 RZ (rseq_z_range _)) (main_cells_4 RZ (rseq_z_range _))). Qed.
End Inst.
