(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm Asanjze AsanInit Starob1 Star2r0 Asanii6.

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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm Asanjze AsanInit Starob1 Asanii6.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.AxSyetn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanz3l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.Asanfbz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanjze OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanInit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Starob1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanii6.
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
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  #[local] Notation SINV := (SINV0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH sp rdraw argv envp uid hw).
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
    intros l H. pose proof (cells_okb_sound sp rdraw brk0 argv envp uid hw fs Hsp Hva cs E R FULL model CS l H) as F.
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
    pose proof (pre_word_img_at sp rdraw brk0 argv envp uid hw fs Hsp Hva cs E R FULL model CS (ELit 0) 0 (ub_lit E) a w ve H
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
    pose proof (pre_word_at sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS b B Ub off w ve H ltac:(lia) Hhi ROM) as X.
    apply bytes_at_of_mb; [lia| rewrite length_word_to_le_bytes; lia|].
    intros i Hi. rewrite length_word_to_le_bytes in Hi. unfold mb. rewrite (X i Hi). symmetry. apply nth_error_nth'. rewrite length_word_to_le_bytes. exact Hi.
  Qed.

  (* [comment removed for export] *)
  Lemma zero_sym : forall b B off n, bv_unsigned (edenot E b) = B -> KH (KZero (SA b off) (ELit n)) = true -> 0 <= n < 2^64 ->
    forall i, 0 <= i < n -> FULL (Z_to_bv 64 (B + off + i)) = Some (Z_to_bv 8 0).
  Proof. intros b B off n Ub H Hn. exact (pre_zero_at sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS b B Ub off n H Hn). Qed.

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
    apply (pre_wr_at sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS b B Ub off n H ltac:(lia) Hn Hhi).
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
    destruct (kimg_zero_range sp rdraw brk0 argv envp uid hw fs Hsp Hva cs E R FULL model CS lo' hi' lo (lo + n) KI H1 H2
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm Asanjze AsanInit Starob1 Star2r0 Asanii6.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanz3l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.Asanfbz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanjze OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanInit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Starob1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Star2r0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanii6.
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
Definition e_rnd : expr :=
  EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1))
    (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 4)) (EMd Instr.M_MUL (ELit 16) (EVar 6))))).
Definition K_RNDBLOB : nat := 25%nat.

(* [comment removed for export] *)
Definition entry_keys : list kentry :=
  [ KWr (SA (ELit 0) 0xa8000) (ELit 0x562000);
    KWord (SA (ELit 0) 0x5e8330) 4%nat (EVar 44);
    KRange (EVar 44) 1 4194303;
    KImg 65536 0xab078;
    KZero (SA e_pgsh 2146402304) e_shlen;
    KRange (EVar 10) 0 7;
    KBlob (SA e_rnd 184) (ELit 16) K_RNDBLOB ].
Definition chk_entry (cs : acs) : bool := forallb (fun K => existsb (kentry_eqb K) (kn cs)) entry_keys.

Lemma chk_entry_1 : chk_entry HS_asan2_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma chk_entry_2 : chk_entry HS_asan2_2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma chk_entry_3 : chk_entry HS_asan2b_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma chk_entry_4 : chk_entry HS_asan2b_2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma main_cells_1 : cells_okb HS_asan2_1 DA_Entry.MAIN_CELLS = true. Proof. vm_compute. reflexivity. Qed.
Lemma main_cells_2 : cells_okb HS_asan2_2 DA_Entry.MAIN_CELLS = true. Proof. vm_compute. reflexivity. Qed.
Lemma main_cells_3 : cells_okb HS_asan2b_1 DA_Entry.MAIN_CELLS = true. Proof. vm_compute. reflexivity. Qed.
Lemma main_cells_4 : cells_okb HS_asan2b_2 DA_Entry.MAIN_CELLS = true. Proof. vm_compute. reflexivity. Qed.
End Asannjs.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.FileSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.AxSyetn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanz3l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.Asanfbz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanjze OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanInit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Starob1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Star2r0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanii6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asan9xo.Asanycn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asan9xo.Asannjs.
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
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  #[local] Notation SINV := (SINV0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH sp rdraw argv envp uid hw).
  Context {BL : AsanInit.BootLim}.   (* [comment removed for export] *)
  #[local] Notation LIM := (@AsanInit.blim BL).
  Variable cs : acs.
  Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis CS : cs_ok ASEGS ASAN LIM SINV argH fs E cs R FULL model.
  Hypothesis CHK : chk_all cs = true.
  Hypothesis CHKE : chk_entry cs = true.
  Hypothesis CC : cells_okb cs DA_Entry.MAIN_CELLS = true.
  #[local] Notation usp := (bv_unsigned sp).
  #[local] Notation bsb := (build_stack_bytes APH sp argv envp uid hw rdraw).

  Let MP : main_pre sp rdraw brk0 argv envp uid hw fs R FULL model :=
    main_pre_of_cs_ok sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve cs E R FULL model CHK CS.

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

  (* [comment removed for export] *)
  Lemma strings_fit :
    DA_Entry.e_p0a usp argv envp + DA_Entry.e_L0 argv + 1 <= usp + Z.of_nat (length bsb) - 16 - total_arg_bytes envp
    /\ ((2 <= length argv)%nat ->
        DA_Entry.e_p1a usp argv envp + DA_Entry.e_L1 argv + 1 <= usp + Z.of_nat (length bsb) - 16 - total_arg_bytes envp)
    /\ usp + Z.of_nat (length bsb) <= usp + entry_stack_span argv envp
    /\ 0 <= total_arg_bytes envp.
  Proof.
    pose proof (length_bsb_eq APH sp rdraw argv envp uid hw) as LB. pose proof (build_stack_bytes_within_span APH sp argv envp uid hw rdraw) as SB.
    unfold stack_image_size in LB. cbv zeta in LB.
    unfold DA_Entry.e_p1a, DA_Entry.e_p0a, DA_Entry.e_L0, DA_Entry.e_L1, DA_Entry.e_argc, DA_Entry.e_envc.
    pose proof (tab_nonneg envp) as TE. pose proof (tab_ge1 argv argc_ge1) as G1.
    match type of LB with _ = ?len + (8 - ?len mod 8) mod 8 + 16 =>
      assert (PD : 0 <= (8 - len mod 8) mod 8 < 8) by (apply Z.mod_pos_bound; lia) end.
    split; [lia|]. split; [| split; [lia| exact TE]].
    intros H2. pose proof (tab_ge2 argv H2) as G2. lia.
  Qed.

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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Str.
    Variable k : nat.
    Hypothesis Hk : (k < length argv)%nat.
    Hypothesis Hk2 : (k <= 1)%nat.
    Let pk : Z := usp + 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 184 + total_arg_bytes (firstn k argv).
    Let sk : list byte := nth k argv [].

    Lemma tab_firstn_le : total_arg_bytes (firstn k argv) + Z.of_nat (length sk) + 1 <= total_arg_bytes argv.
    Proof. subst sk. exact (tab_firstn_gen argv k Hk). Qed.

    Lemma pk_range : usp <= pk /\ pk + Z.of_nat (length sk) + 1 <= usp + Z.of_nat (length bsb) - 16 /\ usp + Z.of_nat (length bsb) <= 2^47.
    Proof.
      pose proof (length_bsb_eq APH sp rdraw argv envp uid hw) as LB. pose proof (build_stack_bytes_within_span APH sp argv envp uid hw rdraw) as SB.
      unfold stack_image_size in LB. cbv zeta in LB. pose proof usp_facts as (U1 & U2 & U3).
      pose proof (tab_nonneg envp). pose proof (tab_nonneg (firstn k argv)). pose proof tab_firstn_le.
      match type of LB with _ = ?len + (8 - ?len mod 8) mod 8 + 16 =>
        assert (PD : 0 <= (8 - len mod 8) mod 8 < 8) by (apply Z.mod_pos_bound; lia) end.
      subst pk. lia.
    Qed.

    Lemma cat_argv_ptr_val : cat_argv_ptr sp argv envp k = Z_to_bv 64 pk.
    Proof.
      pose proof pk_range as (P1 & P2 & P3). pose proof usp_facts as (U1 & _). unfold sp_window_lo in U1.
      rewrite (cat_argv_ptr_offset sp argv envp k Hk). unfold cat_string_base, cat_struct_size.
      apply bv_eq. rewrite !bv_add_unsigned. unfold nat_to_word. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
      change (bv_modulus 64) with (2^64).
      rewrite <- !total_arg_bytes_Z. pose proof (tab_nonneg (firstn k argv)) as T0.
      rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul. unfold auxv_size.
      change (Z.of_nat 8) with 8. change (Z.of_nat 1) with 1. change (Z.of_nat 160) with 160.
      subst pk. Z.div_mod_to_equations. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma str_argH : forall j, (j < length sk + 1)%nat -> argH0 APH sp rdraw argv envp uid hw E (Z_to_bv 64 (pk + Z.of_nat j)) = true.
    Proof.
      intros j Hj. pose proof pk_range as (P1 & P2 & P3). pose proof usp_facts as (U1 & _). unfold sp_window_lo in U1.
      pose proof (W_range APH sp rdraw argv envp uid hw Hva Hve) as (W1 & W2 & W3).
      pose proof (tab_nonneg (firstn k argv)).
      unfold argH0. cbv zeta. rewrite u_lit64a, Z.mod_small by lia.
      apply orb_true_iff. right. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; subst pk; lia.
    Qed.

    Lemma str_bytes : Lbytes_at FULL pk (sk ++ [Z_to_bv 8 0]).
    Proof.
      pose proof pk_range as (P1 & P2 & P3). pose proof usp_facts as (U1 & _). unfold sp_window_lo in U1.
      assert (LEN : length (sk ++ [Z_to_bv 8 0]) = (length sk + 1)%nat) by (rewrite length_app; reflexivity).
      apply bytes_at_pointwise; [lia| rewrite LEN; lia|]. rewrite LEN.
      (* [comment removed for export] *)
      assert (RD : rdn ASEGS FULL (Z_to_bv 64 pk) (length sk + 1) = Some (sk ++ [Z_to_bv 8 0])).
      { rewrite (rdn_ext FULL (wrap_mem APH sp argv envp uid hw rdraw)).
        - rewrite (rdn_wrap_stack_above ASEGS APH sp argv envp (Z_to_bv 64 pk) (length sk + 1) uid hw rdraw)
            by (rewrite u_lit64a, Z.mod_small; lia).
          rewrite <- cat_argv_ptr_val. subst sk. apply (read_argv_cstr_k APH ASEGS sp argv envp k uid hw rdraw Hk). lia.
        - intros j Hj. rewrite u_lit64a, Z.mod_small by lia.
          exact (proj2 (pre_sinv sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS) _ (str_argH j Hj)). }
      assert (SEG : forall i, (i < length sk + 1)%nat -> seg_rom ASEGS (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 pk) + Z.of_nat i)) = None).
      { intros i Hi. apply (seg_rom_off_hull ASEGS ASAN asan_in_hull). unfold in_hull.
        rewrite u_lit64a, Z.mod_small, u_lit64a, Z.mod_small by (rewrite ?u_lit64a, ?Z.mod_small; lia).
        cbn [img_lo img_hi ASAN]. apply andb_false_iff. right. apply Z.ltb_ge. lia. }
      intros j Hj. pose proof (rdn_bytes FULL (length sk + 1) (Z_to_bv 64 pk) _ SEG RD j Hj) as X.
      rewrite u_lit64a, Z.mod_small in X by lia. exact X.
    Qed.

    (* [comment removed for export] *)
    Lemma U_rnd : bv_unsigned (edenot E e_rnd) = usp + Z.of_nat (length bsb) - 16 - 184.
    Proof.
      pose proof (W_range APH sp rdraw argv envp uid hw Hva Hve) as (W1 & W2 & W3).
      pose proof usp_facts as (U1 & U2 & U3). unfold sp_window_lo in U1. pose proof pk_range as (_ & _ & P3).
      assert (AR : 1 <= Z.of_nat (length argv) <= 1024) by (pose proof Hva as [H _]; exact H).
      assert (ER : 0 <= Z.of_nat (length envp) <= 256) by (pose proof Hve as [H _]; lia).
      pose proof (pre_v0 sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS) as V0.
      pose proof (pre_v6 sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS) as V6.
      pose proof (pre_v1 sp rdraw brk0 argv envp uid hw fs Hva cs E R FULL model CS) as V1.
      assert (V2 : bv_unsigned (ev E 2%nat) = Z.of_nat (length envp)).
      { rewrite (pre_ev_lt9 sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS 2%nat) by (unfold NX0; lia). unfold E0. cbn [ev vals0 nth].
        rewrite u_lit64a. apply Z.mod_small. lia. }
      assert (V4 : bv_unsigned (ev E 4%nat) = (Z.of_nat (length bsb) - 16 - (8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 184)) / 8).
      { rewrite (pre_ev_lt9 sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS 4%nat) by (unfold NX0; lia). unfold E0. cbn [ev vals0 nth].
        rewrite u_lit64a. apply Z.mod_small. lia. }
      unfold e_rnd. cbn [edenot]. rewrite !u_add64, !u_mul64_boot, !u_lit64a. rewrite V0, V6, V1, V2, V4.
      Z.div_mod_to_equations. lia.
    Qed.
    Hypothesis KHR : khas cs (KBlob (SA e_rnd 184) (ELit 16) K_RNDBLOB) = true.
    Lemma rnd_bytes : forall i, 0 <= i < 16 ->
      FULL (Z_to_bv 64 (usp + Z.of_nat (length bsb) - 16 + i)) = Some (nth (Z.to_nat i) (eb E K_RNDBLOB) (Z_to_bv 8 0)).
    Proof.
      intros i Hi.
      pose proof (khas_ok sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS _ KHR) as KB. cbn [kentry_ok] in KB.
      destruct KB as (_ & _ & KB). unfold elenZ, estart in KB. cbn [a_base a_off] in KB. rewrite edenot_lit, u_lit64a in KB.
      specialize (KB i ltac:(change (16 mod 2 ^ 64) with 16; lia)). rewrite U_rnd in KB.
      replace (usp + Z.of_nat (length bsb) - 16 - 184 + 184 + i) with (usp + Z.of_nat (length bsb) - 16 + i) in KB by lia.
      exact (Mr_some sp rdraw argv envp uid hw cs E FULL model _ _ KB).
    Qed.

    (* [comment removed for export] *)
    Lemma block_byte : forall a, usp + 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 184 <= a < usp + Z.of_nat (length bsb) - 16 ->
      FULL (Z_to_bv 64 a) = Some (nth (Z.to_nat (a - usp)) bsb (Z_to_bv 8 0)).
    Proof.
      intros a Ha. pose proof usp_facts as (U1 & U2 & U3). unfold sp_window_lo in U1. pose proof pk_range as (_ & _ & P3).
      pose proof (W_range APH sp rdraw argv envp uid hw Hva Hve) as (W1 & W2 & W3).
      assert (AH : argH0 APH sp rdraw argv envp uid hw E (Z_to_bv 64 a) = true).
      { unfold argH0. cbv zeta. rewrite u_lit64a, Z.mod_small by lia.
        apply orb_true_iff. right. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
      rewrite (proj2 (pre_sinv sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS) _ AH).
      unfold wrap_mem, stack_to_mem, entry_stack_image. rewrite u_lit64a, Z.mod_small by lia.
      destruct (Z.leb_spec0 usp a); [| exfalso; lia]. cbn zeta.
      rewrite length_app.
      destruct (Z.ltb_spec0 (a - usp) (Z.of_nat (length bsb + length (entry_slack sp bsb (ed_slack rdraw))))); [| exfalso; lia].
      rewrite nth_error_app1 by lia.
      rewrite (nth_error_nth' bsb (Z_to_bv 8 0)) by lia. reflexivity.
    Qed.

    Lemma str_slack : exists sl, length sl = 16%nat /\ Lbytes_at FULL (pk + Z.of_nat (length sk) + 1) sl.
    Proof.
      pose proof pk_range as (P1 & P2 & P3). pose proof usp_facts as (U1 & _). unfold sp_window_lo in U1.
      set (q := pk + Z.of_nat (length sk) + 1).
      set (e16 := usp + Z.of_nat (length bsb) - 16).
      set (f := fun i : nat => if (q + Z.of_nat i <? e16) then nth (Z.to_nat (q + Z.of_nat i - usp)) bsb (Z_to_bv 8 0)
                               else nth (Z.to_nat (q + Z.of_nat i - e16)) (eb E K_RNDBLOB) (Z_to_bv 8 0)).
      exists (map f (seq 0 16)). split; [rewrite length_map, length_seq; reflexivity|].
      apply bytes_at_pointwise; [subst q; lia| rewrite length_map, length_seq; subst q; cbn; lia|].
      rewrite length_map, length_seq. intros j Hj.
      rewrite (nth_indep _ (Z_to_bv 8 0) (f 0%nat)) by (rewrite length_map, length_seq; exact Hj).
      rewrite map_nth, seq_nth by exact Hj. cbn [Nat.add]. unfold f.
      destruct (Z.ltb_spec0 (q + Z.of_nat j) e16).
      - apply block_byte. subst q e16. pose proof (tab_nonneg (firstn k argv)). subst pk. lia.
      - replace (q + Z.of_nat j) with (e16 + (q + Z.of_nat j - e16)) at 1 by lia. subst e16.
        apply rnd_bytes. subst q. lia.
    Qed.
  End Str.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem entry_raw_of_cs : DA_Entry.entry_raw usp argv envp fs R FULL model.
  Proof.
    pose proof MP as MP'.
    destruct MP' as [Mra Msp Mgp Mtp Ma0 Ma1 Mhalt Mfs Mfds Mlim Mtid Margb Mp0 Mp1 Mstk Mnone Mwords Mext Mzero Mfill].
    pose proof usp_facts as (U1 & U2 & U3). pose proof strings_fit as (SF0 & SF1 & SF2 & SF3).
    assert (U0 : bv_unsigned (edenot E (ELit 0)) = 0) by (cbn [edenot]; rewrite u_lit64a; reflexivity).
    assert (AR : 1 <= Z.of_nat (length argv) <= 1024) by (pose proof Hva as [H _]; exact H).
    assert (ER : 0 <= Z.of_nat (length envp) <= 256) by (pose proof Hve as [H _]; lia).
    unfold sp_window_lo in U1.
    constructor.
    - exact Mra.
    - exact Msp.
    - exact Mgp.
    - exact Mtp.
    - exact Ma0.
    - exact Ma1.
    - unfold DA_Entry.e_span, sp_window_lo. pose proof (entry_stack_span_bound argv envp Hva Hve). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
    - unfold DA_Entry.e_span. lia.
    - unfold DA_Entry.e_span, DA_Entry.e_argc. intros H2. specialize (SF1 ltac:(lia)). lia.
    - exact Mhalt.
    - exact Mfs.
    - exact Mfds.
    - (* [comment removed for export] *)
      exists (bv_unsigned (ev E 44%nat)).
      pose proof (pre_range sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS 44%nat 1 4194303
                    (khas_entry (KRange (EVar 44%nat) 1 4194303) ltac:(cbn; tauto))) as TR.
      split; [lia|].
      pose proof (word_lit_img sp rdraw brk0 argv envp uid hw fs Hsp Hva cs E R FULL model CS 0x5e8330 4%nat (EVar 44%nat)
                    (khas_entry (KWord (SA (ELit 0) 0x5e8330) 4%nat (EVar 44%nat)) ltac:(cbn; tauto)) ltac:(cbn; lia) ltac:(cbn; lia)) as TW.
      unfold Mem.le4. rewrite u_lit64a, Z.mod_small by lia. exact TW.
    - (* [comment removed for export] *)
      exact (cells_bytes sp rdraw brk0 argv envp uid hw fs Hsp Hva cs E R FULL model CS _ CC).
    - (* [comment removed for export] *)
      intros a Ha.
      pose proof (khas_ok sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS _ (khas_entry (KWr (SA (ELit 0) 0xa8000) (ELit 0x562000)) ltac:(cbn; tauto))) as KW.
      destruct KW as [_ KW].
      rewrite (estart_at E (ELit 0) 0 U0), (elenZ_lit E) in KW by lia.
      specialize (KW (a - 0xa8000) 1%nat ltac:(lia) ltac:(cbn; lia)).
      replace (0 + 688128 + (a - 688128)) with a in KW by lia.
      apply wview_Mr_FULL. cbn [store_ok] in KW.
      destruct (wview ASEGS (Mr ASAN argH E cs model FULL) (Z_to_bv 64 a)); [discriminate| discriminate].
    - (* [comment removed for export] *)
      intros a Ha. apply (Mnone 65536 0xab078 a); [unfold IMG_NONE; left; reflexivity| lia].
    - (* [comment removed for export] *)
      intros a Ha. unfold DA_Entry.STK_LO in Ha.
      replace a with (Asanii6.usp sp - 8388608 + (a - (usp - 8388608))) by (unfold Asanii6.usp; lia).
      apply Mstk. lia.
    - (* [comment removed for export] *)
      intros a Ha. unfold DA_Entry.STKSH_LO, DA_Entry.STKSH_HI, AIface.sh, kShadowOffset in Ha. rewrite HCEIL in Ha.
      pose proof (khas_ok sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS _ (khas_entry (KZero (SA e_pgsh 2146402304) e_shlen) ltac:(cbn; tauto))) as KZ.
      cbn [kentry_ok] in KZ. destruct KZ as [_ KZ]. unfold elenZ, estart in KZ. cbn [a_base a_off] in KZ.
      pose proof (pre_v0 sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS) as V0.
      assert (V10 : bv_unsigned (ev E 10%nat) = (usp mod 32768) / 4096).
      { rewrite (pre_ev_lt9 sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS 10%nat) by (unfold NX0; lia). unfold E0. cbn [ev vals0 nth].
        rewrite u_lit64a. apply Z.mod_small. Z.div_mod_to_equations. lia. }
      assert (PG : bv_unsigned (edenot E e_pgsh) = 4096 * (usp / 32768) + 512 * ((usp mod 32768) / 4096)).
      { unfold e_pgsh. cbn [edenot]. rewrite !u_add64, !u_mul64_boot, !u_lit64a. rewrite V0, V10. Z.div_mod_to_equations. lia. }
      assert (LN : bv_unsigned (edenot E e_shlen) = 17592187092992 - (4096 * (usp / 32768) + 512 * ((usp mod 32768) / 4096))).
      { unfold e_shlen. cbn [edenot]. rewrite !u_add64, !u_mul64_boot, !u_lit64a. rewrite V0, V10. Z.div_mod_to_equations. lia. }
      rewrite PG, LN in KZ.
      specialize (KZ (a - (4096 * (usp / 32768) + 512 * (usp mod 32768 / 4096) + 2146402304)) ltac:(Z.div_mod_to_equations; lia)).
      match type of KZ with ?M (Z_to_bv 64 ?x) = _ => replace x with a in KZ by lia end.
      exact (Mr_some sp rdraw argv envp uid hw cs E FULL model _ _ KZ).
    - (* [comment removed for export] *)
      apply bytes_at_pointwise; rewrite ?Mem.length_le8; [lia| cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
      intros j Hj. exact (Mp0 j Hj).
    - (* [comment removed for export] *)
      intros H2. apply bytes_at_pointwise; rewrite ?Mem.length_le8; [lia| cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
      intros j Hj. exact (Mp1 H2 j Hj).
    - (* [comment removed for export] *)
      pose proof (str_bytes 0%nat ltac:(lia) ltac:(lia)) as X. cbn [firstn] in X.
      replace (total_arg_bytes []) with 0 in X by reflexivity.
      unfold DA_Entry.e_p0a, DA_Entry.e_argc, DA_Entry.e_envc. rewrite Z.add_0_r in X. exact X.
    - (* [comment removed for export] *)
      intros H2. unfold DA_Entry.e_argc in H2.
      pose proof (str_bytes 1%nat ltac:(lia) ltac:(lia)) as X.
      unfold DA_Entry.e_p1a, DA_Entry.e_p0a, DA_Entry.e_L0, DA_Entry.e_argc, DA_Entry.e_envc.
      replace (total_arg_bytes (firstn 1 argv)) with (Z.of_nat (length (nth 0 argv [])) + 1) in X.
      + match goal with |- Mem.bytes_at _ _ ?a _ => match type of X with Mem.bytes_at _ _ ?b _ => replace a with b by lia end end. exact X.
      + generalize H2. clear. destruct argv as [|a l]; [cbn; lia| intros _]. cbn [firstn nth]. rewrite tab_cons.
        change (firstn 0 l) with (@nil (list byte)). change (total_arg_bytes []) with 0. lia.
    - (* [comment removed for export] *)
      destruct (str_slack 0%nat ltac:(lia) ltac:(lia) (khas_entry _ ltac:(unfold entry_keys; cbn [In]; do 6 right; left; reflexivity))) as (sl & L & B).
      exists sl. split; [exact L|]. cbn [firstn nth] in B. replace (total_arg_bytes []) with 0 in B by reflexivity.
      unfold DA_Entry.e_p0a, DA_Entry.e_L0, DA_Entry.e_argc, DA_Entry.e_envc. rewrite Z.add_0_r in B. exact B.
    - (* [comment removed for export] *)
      intros H2. unfold DA_Entry.e_argc in H2.
      destruct (str_slack 1%nat ltac:(lia) ltac:(lia) (khas_entry _ ltac:(unfold entry_keys; cbn [In]; do 6 right; left; reflexivity))) as (sl & L & B).
      exists sl. split; [exact L|].
      unfold DA_Entry.e_p1a, DA_Entry.e_p0a, DA_Entry.e_L0, DA_Entry.e_L1, DA_Entry.e_argc, DA_Entry.e_envc.
      replace (total_arg_bytes (firstn 1 argv)) with (Z.of_nat (length (nth 0 argv [])) + 1) in B.
      + match goal with |- Mem.bytes_at _ _ ?a _ => match type of B with Mem.bytes_at _ _ ?b _ => replace a with b by lia end end. exact B.
      + generalize H2. clear. destruct argv as [|a l]; [cbn; lia| intros _]. cbn [firstn nth]. rewrite tab_cons.
        change (firstn 0 l) with (@nil (list byte)). change (total_arg_bytes []) with 0. lia.
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
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Context {BL : AsanInit.BootLim}.   (* [comment removed for export] *)
  #[local] Notation CSOK HS E R FULL model :=
    (cs_ok ASEGS ASAN (@AsanInit.blim BL) (SINV0 APH sp rdraw brk0 argv envp uid hw) (argH0 APH sp rdraw argv envp uid hw) fs E HS R FULL model).

  Theorem entry_raw_1 : forall E R FULL model, CSOK HS_asan2_1 E R FULL model -> DA_Entry.entry_raw (bv_unsigned sp) argv envp fs R FULL model.
  Proof. intros E R FULL model HC. exact (entry_raw_of_cs sp HCEIL rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit HS_asan2_1 E R FULL model HC chk_all_1 chk_entry_1 main_cells_1). Qed.
  Theorem entry_raw_2 : forall E R FULL model, CSOK HS_asan2_2 E R FULL model -> DA_Entry.entry_raw (bv_unsigned sp) argv envp fs R FULL model.
  Proof. intros E R FULL model HC. exact (entry_raw_of_cs sp HCEIL rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit HS_asan2_2 E R FULL model HC chk_all_2 chk_entry_2 main_cells_2). Qed.
  Theorem entry_raw_3 : forall E R FULL model, CSOK HS_asan2b_1 E R FULL model -> DA_Entry.entry_raw (bv_unsigned sp) argv envp fs R FULL model.
  Proof. intros E R FULL model HC. exact (entry_raw_of_cs sp HCEIL rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit HS_asan2b_1 E R FULL model HC chk_all_3 chk_entry_3 main_cells_3). Qed.
  Theorem entry_raw_4 : forall E R FULL model, CSOK HS_asan2b_2 E R FULL model -> DA_Entry.entry_raw (bv_unsigned sp) argv envp fs R FULL model.
  Proof. intros E R FULL model HC. exact (entry_raw_of_cs sp HCEIL rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit HS_asan2b_2 E R FULL model HC chk_all_4 chk_entry_4 main_cells_4). Qed.
End Inst.
