(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Notation amem := (word -> option byte).
Definition AMALLOC_SYM : Z := 0x532d4.
Definition AFREE_SYM : Z := 0x532d0.
Definition AMALLOC_PC : Z := 0x53570.
Definition AFREE_PC : Z := 0x53410.
Definition AMALLOC_STACK : Z := 4096.
Definition AFREE_STACK : Z := 4096.
Definition ATP : Z := 0x5d5410.
Definition AREQMAX : Z := 2^29 - 2^16.
Definition UDEPTH : nat := 28%nat.
Definition AIMG_LO : Z := 0x10000.
Definition AIMG_HI : Z := 0x5f7000.
Definition ARELRO_LO : Z := 0x99000.
Definition ARELRO_HI : Z := 0x9b000.
Definition KLS : Z := 0x7fff7000.
Definition sclr (a n : Z) : Prop := a + n <= KLS \/ 0x10007fff8000 <= a.
Definition iclr (a n : Z) : Prop := 4096 <= a /\ (a + n <= AIMG_LO \/ AIMG_HI <= a).
Section ABLK. Context {rc : runConstT}.
Definition ablk (lo hi : Z) : Prop := (AIMG_HI <= lo /\ hi <= KLS) \/ (0x10007fff8000 <= lo /\ hi <= ATOP).
#[using="Type"] Lemma ablk_sub : forall lo hi lo' hi', ablk lo hi -> lo <= lo' -> hi' <= hi -> ablk lo' hi'.
Proof. intros lo hi lo' hi' H A B. unfold ablk, AIMG_HI, KLS in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010=62146360207.900000:S1H1A1B2H0".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma ablk_lin : forall lo hi, ablk lo hi -> AIMG_HI <= lo /\ 0 <= lo /\ hi <= ATOP /\ hi + 8 <= 2^47.
Proof. intros lo hi H. atop_facts. unfold ablk, AIMG_HI, KLS in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010=56824890759.5000006S1H2H0".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma ablk_app_blk : forall lo hi, ablk lo hi -> lo <= hi -> app_blk lo hi.
Proof. intros lo hi H LE. atop_facts. unfold ablk, app_blk, AIMG_HI, KLS, KLOW, KHIGH, KEND in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010=48425434542.6000009S1H2LE2H0".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma ablk_clear_band : forall lo hi a, ablk lo hi -> KLS <= a < 0x10007fff8000 -> ~ (lo <= a < hi).
Proof. intros lo hi a H B. unfold ablk, AIMG_HI, KLS in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010=53505208473.7000005S1H1B".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma ablk_disj_band : forall lo hi, ablk lo hi -> hi <= KLS \/ 0x10007fff8000 <= lo.
Proof. intros lo hi H. unfold ablk in H. Local Ltac2 Set LiaHints.tbl := fun () => "0010=32688493423.5000003S1H".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma shad_in_band : forall a, 0 <= a < 2^47 -> KLS + 4096 <= shad a < 0x10007fff8000.
Proof. intros a H. rewrite shad_div. unfold KLS, ASHOFF. Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0010>50430762390.10000009S1H2H02H1".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End ABLK.
Definition artcells (m : amem) : Prop :=
rw_cells asegs m 0x99760 [C8 (Z_to_bv 64 0x131f20)]
/\ rw_cells asegs m 0x99770 [C8 (Z_to_bv 64 0x133fa8); C8 (Z_to_bv 64 0x9fc78); C8 (Z_to_bv 64 0xa2478);
C8 (Z_to_bv 64 0xa3168); C8 (Z_to_bv 64 0xa3170); C8 (Z_to_bv 64 0xa3160)]
/\ rw_cells asegs m 0x9a2e8 [C8 (Z_to_bv 64 0xa3159)]
/\ rw_cells asegs m 0x9b5e0 [C8 (Z_to_bv 64 0x92ab0); C8 (Z_to_bv 64 0x92eb4)]
/\ rw_cells asegs m 0xa2478 [C8 (Z_to_bv 64 0x7fff8000)]
/\ rw_cells asegs m 0xa2480 [C4 (Z_to_bv 64 1)]
/\ rw_cells asegs m 0xa3158 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]
/\ rw_cells asegs m 0xa3160 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
/\ rw_cells asegs m 0xa1cdc [C1 (Z_to_bv 8 1)]
/\ rw_cells asegs m 0xa317c [C4 (Z_to_bv 64 30)]
/\ rw_cells asegs m 0x131f20 [C8 (Z_to_bv 64 4096)]
/\ rw_cells asegs m 0x133fc8 [C8 (Z_to_bv 64 0x1e00010000)]
/\ rw_cells asegs m 0x134020 [C8 (Z_to_bv 64 0xffffffffffffffff)]
/\ rw_cells asegs m 0x9b4d8 [C8 (Z_to_bv 64 0x92400); C8 (Z_to_bv 64 0x8f2f0)]
/\ rw_cells asegs m 0x9b590 [C8 (Z_to_bv 64 0x9333c)]
/\ rw_cells asegs m 0x9b4b8 [C8 (Z_to_bv 64 0x981b4)]
/\ rw_cells asegs m 0x9b4c0 [C8 (Z_to_bv 64 0x8f068)]
/\ rw_cells asegs m 0x9b590 [C8 (Z_to_bv 64 0x9333c)]
/\ rw_cells asegs m 0x9b4a8 [C8 (Z_to_bv 64 0x929b4)]
/\ rw_cells asegs m 0x133ff8 [C8 (Z_to_bv 64 4294967296)]
/\ rw_cells asegs m 0x1340a0 [C8 (Z_to_bv 64 0x101010101010101)]
/\ rw_cells asegs m 0x9fcd8 [C1 (Z_to_bv 8 1)]
/\ rw_cells asegs m 0x131f18 [C4 (Z_to_bv 64 0)].
Definition in_ranges (l : list (Z * Z)) (a : Z) : Prop := exists iv, In iv l /\ fst iv <= a < snd iv.
Definition AINSTANCE : Z := 0x9ee18.
Definition AFLAGS : Z := 0x9fc78.
Definition ACFLAGS : Z := 0x133fa8.
Definition AINITED : Z := 0xa3158.
Definition ACANPOISON : Z := 0xa1cdc.
Definition APGSZ : Z := 0x131f20.
Definition ATSDI : Z := 0xa1ce0.
Definition ATSDK : Z := 0xa1ce4.
Definition ATP88 : Z := 0x5d53b8.
Definition ATSD : Z := 0x5f67b8.
Definition GOT_PGSZ : Z := 0x99760.
Definition GOT_CFLAGS : Z := 0x99770.
Record alayout := mkALayout {
al_V : nat -> Z;
al_w : bool;
al_U : list (list Z)
}.
Definition al_sp0 (L : alayout) : Z := 32768 * al_V L 0%nat + 16 * al_V L 6%nat.
Definition al_top (L : alayout) : Z := page_round_up_Z (al_sp0 L - 0xa0).
Definition al_bot (L : alayout) : Z := al_top L - 0x800000.
Definition al_t (L : alayout) : Z := 4096 * al_V L 240%nat.
Definition al_ctx (L : alayout) : Z := 4096 * al_V L 241%nat.
Definition al_space_beg (L : alayout) : Z := 4096 * (al_V L 221%nat - al_V L 222%nat) + 0x10000.
Definition al_ptr_array (L : alayout) : Z := 4096 * al_V L 239%nat.
Definition al_nodes (L : alayout) : Z := 4096 * al_V L 485%nat.
Definition al_store (L : alayout) : Z := 4096 * al_V L 486%nat.
Definition al_fake (L : alayout) : Z := 4096 * al_V L 406%nat.
Definition AUMAX : Z := 4096.
Inductive abkind := ABHeap (p : aptr) | ABFake (cls : Z).
Record ablock := mkABlock { ab_kind : abkind; ab_addr : Z; ab_size : Z }.
Notation HB p A n := (mkABlock (ABHeap p) A n).
Definition in_block (LB : list ablock) (a : Z) : Prop :=
exists b, In b LB /\ ab_addr b <= a < ab_addr b + ab_size b.
Definition in_fake (LB : list ablock) (a : Z) : Prop :=
exists cls A n, In (mkABlock (ABFake cls) A n) LB /\ A <= a < A + n.
Definition abkind_eqb (k k' : abkind) : bool :=
match k, k' with
| ABHeap p, ABHeap p' => (p =? p')%N
| ABFake c, ABFake c' => c =? c'
| _, _ => false
end.
Definition lb_remove (p : aptr) (LB : list ablock) : list ablock :=
filter (fun b => negb (abkind_eqb (ab_kind b) (ABHeap p))) LB.
Definition hb_ids (LB : list ablock) : list aptr :=
flat_map (fun b => match ab_kind b with ABHeap p => [p] | ABFake _ => [] end) LB.
Definition ablock_range {rc : runConstT} (A n : Z) : Prop :=
ablk A (A + n) /\ 0 <= n /\ A + n <= ATOP /\ A mod 16 = 0.
Definition ablock_shadow (m : amem) (A n : Z) : Prop :=
forall g, 0 <= g -> 8 * g < n ->
m (wa (shad A + g)) = Some (Z_to_bv 8 (if 8 * g + 8 <=? n then 0 else n - 8 * g)).
Inductive uchain (m : amem) (top pc : Z) : Z -> Z -> nat -> list Z -> Prop :=
| uc_stop : forall prev frame k,
~ (prev < frame /\ frame < top - 16 /\ frame mod 8 = 0 /\ (0 < k)%nat) ->
uchain m top pc prev frame k []
| uc_lowpc : forall prev frame k fp ra,
prev < frame -> frame < top - 16 -> frame mod 8 = 0 -> (0 < k)%nat ->
bytes_at asegs m (frame - 16) (le8 (Z_to_bv 64 fp)) ->
bytes_at asegs m (frame - 8) (le8 (Z_to_bv 64 ra)) ->
0 <= ra < 4096 ->
uchain m top pc prev frame k []
| uc_step : forall prev frame k fp ra tr,
prev < frame -> frame < top - 16 -> frame mod 8 = 0 -> (0 < k)%nat ->
bytes_at asegs m (frame - 16) (le8 (Z_to_bv 64 fp)) ->
bytes_at asegs m (frame - 8) (le8 (Z_to_bv 64 ra)) ->
4096 <= ra < 2^64 -> 0 <= fp < 2^64 ->
uchain m top pc frame fp (if ra =? pc then k else Nat.pred k) tr ->
uchain m top pc prev frame k ((if ra =? pc then [] else [ra]) ++ tr).
Lemma uchain_frame : forall m m' top pc prev frame k tr,
uchain m top pc prev frame k tr ->
(forall a, frame - 16 <= a < top -> m' (wa a) = m (wa a)) ->
uchain m' top pc prev frame k tr.
Proof.
intros m m' top pc prev frame k tr H. induction H as [prev frame k Hn | prev frame k fp ra H1 H2 H3 H4 B1 B2 Hra | prev frame k fp ra tr H1 H2 H3 H4 B1 B2 Hra Hfp HC IH]; intros HM.
- apply uc_stop. exact Hn.
- eapply uc_lowpc; eauto.
+ destruct B1 as (X & Y & B). split; [exact X|]. split; [exact Y|]. intros i Hi. rewrite <- (B i Hi). unfold mrd. rewrite HM; [reflexivity|]. rewrite length_le8 in Hi. Local Ltac2 Set LiaHints.tbl := fun () => "0050>12929811680.2436710585164.2136710585164.2559308580184.3059310676304.3300000700>00E00Q00]S2LT2HaS2H22HiS2H22HiS2H42GE1H2H6S2H42GE1H2H6".
lia.
+ destruct B2 as (X & Y & B). split; [exact X|]. split; [exact Y|]. intros i Hi. rewrite <- (B i Hi). unfold mrd. rewrite HM; [reflexivity|]. rewrite length_le8 in Hi. lia.
- eapply uc_step; eauto.
+ destruct B1 as (X & Y & B). split; [exact X|]. split; [exact Y|]. intros i Hi. rewrite <- (B i Hi). unfold mrd. rewrite HM; [reflexivity|]. rewrite length_le8 in Hi. lia.
+ destruct B2 as (X & Y & B). split; [exact X|]. split; [exact Y|]. intros i Hi. rewrite <- (B i Hi). unfold mrd. rewrite HM; [reflexivity|]. rewrite length_le8 in Hi. lia.
+ destruct (Z_lt_le_dec frame fp) as [LT|GE].
* apply IH. intros a Ha. apply HM. lia.
*
inversion HC; subst; [apply uc_stop; assumption | exfalso; lia | exfalso; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
