(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySweepS3b), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8v.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySweepS3b.v, with its module paths changed; 571 of its 687 lines of code are new or changed and 1078 lines of the source are left out. *)
(* Segment 3, part a, of the sweep phase of fuzz_grant's entry function on IMAGE B:
   0x81618 .. 0x8173c (fuzz_grant.c:325-327) — the first group-A loop: for p = 0, 1, 2
   the harness calls want_of(was_set, set_to, a.base, p) (0x8163c) for the value it
   wants and check_groupa on sweep row 1 + p (0x81654); then the block 0x81668 .. 0x81680
   reads a.width and goes on to the second group-A loop (0x81684, c = 1) or, when the
   width is below 2, through 0x8171c .. 0x81738 to the group-B loop (0x8173c, i = 0).
   One branch is refuted here: the UBSan pointer-overflow guard `bltu a0,s2` into the
   trap 0x81f48 (0x8161c), as slot 88 holds 2^64 - 1 - s and the sweep buffer s lies
   below the allocator's ceiling. The ground this walk stands on is
   LLVMFEntrySweepS1c.v and LLVMFEntrySweepS3c.v; the two calls are LLVMFEntrySweepS3d.v.

   Adapted from lib/A/Prog/GrantEntrySweepS3a.v (a working branch afd75724b5b, blob bc91463cd, 1011 lines),
   which carries no licence header of its own.
   Image B calls want_of where image A reads was_set and set_to in line and calls reac_headamp_default, reloads `a`, the two frame arrays and the table from spill slots 120, 136, 128 and 152, keeps the row, its offset and the bound in s9, s2 and s4, and guards each turn with a UBSan check against slot 88. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaRun PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantPa GrantPaLib GrantRo GrantBContracts
LLVMFEntryDefs LLVMFEntrySweepDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC1g YC1h YC45 YC85 GrantFrame GrantACja.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import LLVMFEntrySeat.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel GrantModel GrantSweepModel BuildSweepModel SweepRowCheck GrantSlotPlan.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require SlotNeeds_c SegSetModel.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* Image A's text was written with this flag false; `Local` keeps the setting here. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
LLVMFEntrySweepS1c LLVMFEntrySweepS3c LLVMFEntrySweepS3d.

(* ---- the model facts of one turn ---- *)
Lemma nth_map_bu : forall (l : list byte) i,
  nth i (map (fun b : byte => bv_unsigned b) l) 0 = bv_unsigned (nth i l (Z_to_bv 8 0)).
Proof. induction l as [|x l IH]; intros [|i]; cbn [map nth]; try reflexivity. apply IH. Qed.

Lemma nth_concat34 : forall (L : list (list byte)) k j, Forall (fun r => length r = 34%nat) L ->
  (k < length L)%nat -> (j < 34)%nat ->
  nth (34 * k + j) (concat L) (Z_to_bv 8 0) = nth j (nth k L []) (Z_to_bv 8 0).
Proof.
  induction L as [|r L IH]; intros k j HF Hk Hj; cbn [length] in Hk; [lia|].
  inversion HF as [|r0 L0 Hr HL]; subst. cbn [concat].
  destruct k as [|k].
  - cbn [nth]. replace (34 * 0 + j)%nat with j by lia. apply app_nth1. lia.
  - rewrite app_nth2 by lia. rewrite Hr. replace (34 * S k + j - 34)%nat with (34 * k + j)%nat by lia.
    cbn [nth]. apply IH; [exact HL | lia | exact Hj].
Qed.

(* Row 1 + p of the sweep is Pau's group-A row for the channel `base` and the value
   the table gives (SweepRowCheck.v nth_row_A0, vz_sweep_vals). *)
Lemma sweep_row_ga0 : forall T t base w (p : nat) j, (1 <= w)%nat -> (p < 3)%nat -> (j < 34)%nat ->
  0 <= base < 48 ->
  nth (34 * (1 + p) + j) (map (fun b : byte => bv_unsigned b) (SWEEP base w (sweep_vals T t base w))) 0 =
  nth j (GAz base (Z.of_nat p) (eff T t base (Z.of_nat p))) 0.
Proof.
  intros T t base w p j Hw Hp Hj Hb.
  rewrite nth_map_bu, SWEEP_rows.
  rewrite nth_concat34; [| apply Forall_rowok_len, sweep_rows_ok | | exact Hj].
  2:{ pose proof (length_sweep_rows base w (sweep_vals T t base w) Hw). lia. }
  rewrite nth_row_A0 by exact Hp. unfold ga_row.
  unfold vz. rewrite (nth_sweep_vals T t base w 0 p) by lia. rewrite bv8_small by apply eff_range.
  rewrite Z.add_0_r, Z.mod_small by lia.
  pose proof (eff_range T t base (Z.of_nat p)) as Hv.
  rewrite <- nth_map_bu. unfold GA. rewrite map_unsigned_bl; [reflexivity|].
  apply GA_bytes_range; lia.
Qed.

(* ---- the symbolic states of this part ---- *)
(* Every stop of this part (the loop's head 0x81618, the return of want_of 0x81640 and
   the return of check_groupa 0x81658) is seated on the same two regions, both
   read-only. Atoms: 32 the one's complement of the sweep buffer (slot 88), 33 the
   address of `a` (slot 120), 34 and 35 the addresses of set_to and was_set (slots 128
   and 136), 36 and 37 a.base and a.width (the two bytes of `a`), 38 the table
   (slot 152). Image A kept the address of `a` in s2 and the table in s4; image B
   reloads both from the machine frame after every call. *)
Definition GPS_want0 : Z := 0xc04.   (* 0x81640, after want_of      *)
Definition GPS_cga0 : Z := 0xc1c.    (* 0x81658, after check_groupa *)
Definition RS0 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 192 0 0
    [YP09.mkChunk 88 (CVal 8 (SOff 32 0)); YP09.mkChunk 120 (CVal 8 (SOff 33 0));
     YP09.mkChunk 128 (CVal 8 (SOff 34 0)); YP09.mkChunk 136 (CVal 8 (SOff 35 0));
     YP09.mkChunk 152 (CVal 8 (SOff 38 0))].
Definition RA0 : YP09.region :=
  YP09.mkRegion (Some 33%nat) 0 2 0 0
    [YP09.mkChunk 0 (CVal 1 (SOff 36 0)); YP09.mkChunk 1 (CVal 1 (SOff 37 0))].
Definition g0_regions : YP09.smem := [RS0; RA0].
Definition ss_g0 (pc : Z) : sstate := mkSS pc sr_atoms g0_regions None (mkFacts [] [] []).

(* The registers a turn keeps from the head of the loop to the return of check_groupa. *)
Definition g0_kl : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 25; 26; 27]%bv.
(* The same and s5 = p + 1, s8 = a.base, which the run to want_of sets. *)
Definition g0_kl2 : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%bv.
(* The registers the runs after check_groupa leave as they found them. *)
Definition g0_kl1 : list (bv 5) := [2; 3; 4; 8; 9; 19; 20; 27]%bv.
Lemma in_bv5 : forall (r : bv 5) (l : list (bv 5)),
  existsb (fun x : bv 5 => bv_unsigned x =? bv_unsigned r) l = true -> In r l.
Proof.
  intros r l. induction l as [|x l IH]; cbn [existsb In]; [discriminate|].
  intros H. apply orb_prop in H as [H|H]; [left; apply bv_eq; apply Z.eqb_eq; exact H | right; apply IH; exact H].
Qed.
Ltac kl_in := apply in_bv5; vm_compute; reflexivity.
Lemma zeq64 : forall a b : Z, a = b -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros a b ->. reflexivity. Qed.
Lemma zeq64m : forall a b : Z, a mod 2 ^ 64 = b mod 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof.
  intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). exact H.
Qed.
(* `lbu` of a byte the engine holds as an atom: the byte zero-extended, which is itself. *)
Lemma zext8_lit : forall v, 0 <= v < 256 -> zext 64 (bv_extract 0 8 (Z_to_bv 64 v)) = Z_to_bv 64 v.
Proof.
  intros v Hv.
  change (zext 64 (bv_extract 0 8 (Z_to_bv 64 v))) with (Z_to_bv 64 (bv_unsigned (bv_extract 0 8 (Z_to_bv 64 v)))).
  f_equal. rewrite bv_extract_unsigned. cbn [Z.of_N]. rewrite Z.shiftr_0_r, unsigned_lit_small by lia.
  unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hv.
Qed.
Lemma U_zext8 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 -> U E (SExt false 8 (SOff n 0)) = v.
Proof.
  intros E n v H Hv. unfold U. cbn [sv_denot]. rewrite H, unsigned_lit_small, Z.add_0_r by lia.
  rewrite zext8_lit by exact Hv. apply unsigned_lit_small. lia.
Qed.
(* The memory a run over read-only regions leaves: the one it started from. *)
Ltac g0_mem HM :=
  lazymatch goal with HFx : frame_of _ ?rs ?m (ms_mem ?msn) |- _ =>
    pose proof (frame_of_read_only _ rs m (ms_mem msn) ltac:(vm_compute; reflexivity) HFx) as HM end;
  cbn [ms_mem mkst] in HM;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* A register the engine gives as an atom plus an offset, as the cut's number. *)
Ltac zreg Q EQ :=
  rewrite Q; rewrite ?EQ; rewrite ?zext8_lit by lia; rewrite ?alu64_add_lit; rewrite ?unsigned_lit_small by lia;
  first [ reflexivity | apply zeq64; lia | apply zeq64m; reflexivity
        | match goal with |- ?g => fail 100 "zreg GOAL" g end ].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma awr_ok_ro : forall E rs STK sp0 FP bl0 blc ly own,
  rs_read_only rs = true -> awr_ok E rs STK sp0 FP bl0 blc ly own.
Proof.
  intros E rs STK sp0 FP bl0 blc ly own H. induction rs as [|r rs IH]; [apply awr_ok_nil|].
  cbn [rs_read_only forallb] in H. apply andb_prop in H as [H1 H2].
  apply awr_ok_cons_ro; [apply Z.leb_le; exact H1 | apply IH; exact H2].
Qed.
(* The write check of a run over read-only regions. *)
Ltac g0_awr := apply awr_ok_ro; vm_compute; reflexivity.
Section b.
Context {PI : PAImg grant_listing}.
Context {RO : ro_below_ofl (@pa_segs _ grant_listing PI) (@pa_relro_lo _ grant_listing PI) (@pa_relro_hi _ grant_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Definition Eg (regs : bvmap 5 word) (xs : list Z) : env := Eimg (Ereg regs (map (Z_to_bv 64) xs)).

Definition g0_xs (cx : ecx) (fp t s : Z) : list Z :=
  [ 2 ^ 64 - 1 - s; gF cx fp + GO_A; gF cx fp + GO_SET; gF cx fp + GO_WAS;
    sw_base (c_pl cx); sw_in (c_pl cx); t ].

Lemma Eg_reg : forall (regs : bvmap 5 word) xs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eg regs xs) n = getr regs r.
Proof. intros regs xs n r Hn. unfold Eg. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma Eg_x : forall (regs : bvmap 5 word) xs j, (32 + j < A_TEXT)%nat -> ew (Eg regs xs) (32 + j) = Z_to_bv 64 (nth j xs 0).
Proof.
  intros regs xs j Hj. unfold Eg. rewrite Eimg_low by exact Hj. rewrite ew_Ereg_extra.
  exact (map_nth (Z_to_bv 64) xs 0 j).
Qed.
Lemma VB : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> YP09.base_val E (Some n) = v.
Proof. intros E n v H Hv. cbn [YP09.base_val]. rewrite H. apply unsigned_lit_small. exact Hv. Qed.
Lemma sv_SOff0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

(* The two bytes of `a`, a.base and a.width, as the region of its address (atom 33). *)
Lemma rok_RA0 : forall E (H : word -> bool) mem A b i,
  ew E 33 = Z_to_bv 64 A -> ew E 36 = Z_to_bv 64 b -> ew E 37 = Z_to_bv 64 i ->
  aview SEGS H mem A = Some b -> aview SEGS H mem (A + 1) = Some i ->
  0 <= A -> A + 2 <= 2 ^ 64 ->
  YP09.region_ok SEGS E (mrestrict H mem) RA0.
Proof.
  intros E H mem A b i E33 E36 E37 Hb Hi HA0 HA1.
  pose proof (gs_val_mem_of_byte H mem A b Hb) as Vb. pose proof (gs_byte_range H mem A b Hb) as Rb.
  pose proof (gs_val_mem_of_byte H mem (A + 1) i Hi) as Vi. pose proof (gs_byte_range H mem (A + 1) i Hi) as Ri.
  unfold YP09.region_ok, RA0. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB E 33 A E33) by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor; [|constructor]].
  - apply (chunk_ok_val SEGS E _ A 0 1 (SOff 36 0) b); [rewrite sv_SOff0; exact E36 | zside | zside |].
    rewrite Z.add_0_r. exact Vb.
  - apply (chunk_ok_val SEGS E _ A 1 1 (SOff 37 0) i); [rewrite sv_SOff0; exact E37 | zside | zside |].
    exact Vi.
Qed.

(* The symbolic state at a stop of this part, from the bytes the cuts name. *)
Lemma g0_seat : forall cx fp t s (W : world SEGS) (regs : bvmap 5 word) mem pc,
  getr regs 9 = w64 (c_sp1 cx) -> 0 <= c_sp1 cx -> c_sp1 cx + 192 <= 2 ^ 64 ->
  0 <= gF cx fp -> gF cx fp + GO_A + 2 <= c_sp1 cx ->
  rdword (aview SEGS (w_H W) mem) (c_sp1 cx + 88) = Some (2 ^ 64 - 1 - s) ->
  rdword (aview SEGS (w_H W) mem) (c_sp1 cx + 120) = Some (gF cx fp + GO_A) ->
  rdword (aview SEGS (w_H W) mem) (c_sp1 cx + 128) = Some (gF cx fp + GO_SET) ->
  rdword (aview SEGS (w_H W) mem) (c_sp1 cx + 136) = Some (gF cx fp + GO_WAS) ->
  rdword (aview SEGS (w_H W) mem) (c_sp1 cx + 152) = Some t ->
  aview SEGS (w_H W) mem (gF cx fp + GO_A) = Some (sw_base (c_pl cx)) ->
  aview SEGS (w_H W) mem (gF cx fp + (GO_A + 1)) = Some (sw_in (c_pl cx)) ->
  st_ok_pi SEGS VAL (Eg regs (g0_xs cx fp t s)) (ss_g0 pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
  intros cx fp t s W regs mem pc R9 Hsp0 Hsp1 HF0 HFA S88 S120 S128 S136 S152 A0 A1.
  rewrite Z.add_assoc in A1.
  rewrite restrict_mkst_fx. unfold ss_g0. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - set (E := Eg regs (g0_xs cx fp t s)).
    assert (U9 : bv_unsigned (ew E 9%nat) = c_sp1 cx).
    { unfold E. rewrite (Eg_reg _ _ 9 9%bv eq_refl), R9. apply unsigned_lit_small. lia. }
    unfold g0_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (gs_slotreg_ok W E mem _ (c_sp1 cx) 0 0 U9 Hsp0 Hsp1 ltac:(intros o Ho; lia)).
      repeat apply Forall_cons; try apply Forall_nil.
      * exact (gs_slot_chunk W E mem 88 32 _ (c_sp1 cx) (Eg_x _ _ 0 ltac:(cbv; lia)) U9 S88).
      * exact (gs_slot_chunk W E mem 120 33 _ (c_sp1 cx) (Eg_x _ _ 1 ltac:(cbv; lia)) U9 S120).
      * exact (gs_slot_chunk W E mem 128 34 _ (c_sp1 cx) (Eg_x _ _ 2 ltac:(cbv; lia)) U9 S128).
      * exact (gs_slot_chunk W E mem 136 35 _ (c_sp1 cx) (Eg_x _ _ 3 ltac:(cbv; lia)) U9 S136).
      * exact (gs_slot_chunk W E mem 152 38 _ (c_sp1 cx) (Eg_x _ _ 6 ltac:(cbv; lia)) U9 S152).
    + apply (rok_RA0 E _ mem (gF cx fp + GO_A) (sw_base (c_pl cx)) (sw_in (c_pl cx))
        (Eg_x _ _ 1 ltac:(cbv; lia)) (Eg_x _ _ 4 ltac:(cbv; lia)) (Eg_x _ _ 5 ltac:(cbv; lia)) A0 A1);
        unfold GO_A in *; lia.
  - set (E := Eg regs (g0_xs cx fp t s)).
    assert (E9 : ew E 9 = Z_to_bv 64 (c_sp1 cx)) by (unfold E; rewrite (Eg_reg _ _ 9 9%bv eq_refl); exact R9).
    assert (E33 : ew E 33 = Z_to_bv 64 (gF cx fp + GO_A)) by exact (Eg_x _ _ 1 ltac:(cbv; lia)).
    unfold g0_regions, RS0, RA0. cbn [YP09.pairwise_disjoint YP09.all_disjoint].
    unfold YP09.extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
    unfold GO_A in *.
    rewrite (VB E 9 _ E9) by lia. rewrite (VB E 33 _ E33) by lia.
    repeat split; lia.
  - split; [exact I | split; exact I].
Qed.

Lemma ap_list : forall (r0 r1 : bvmap 5 word), aregs_preserved r0 r1 ->
  forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r1 r = getr r0 r.
Proof.
  intros r0 r1 H r Hr.
  destruct Hr as [<-|Hr]; [apg H (2%bv : bv 5) 2; reflexivity|].
  destruct Hr as [<-|Hr]; [apg H (3%bv : bv 5) 3; reflexivity|].
  destruct Hr as [<-|Hr]; [apg H (4%bv : bv 5) 4; reflexivity|].
  destruct Hr as [<-|Hr]; [apg H (8%bv : bv 5) 8; reflexivity|].
  destruct Hr as [<-|Hr]; [apg H (9%bv : bv 5) 9; reflexivity|].
  destruct Hr as [<-|Hr]; [apg H (18%bv : bv 5) 18; reflexivity|].
  destruct Hr as [<-|Hr]; [apg H (19%bv : bv 5) 19; reflexivity|].
  destruct Hr as [<-|Hr]; [apg H (20%bv : bv 5) 20; reflexivity|].
  destruct Hr as [<-|Hr]; [apg H (21%bv : bv 5) 21; reflexivity|].
  destruct Hr as [<-|Hr]; [apg H (22%bv : bv 5) 22; reflexivity|].
  destruct Hr as [<-|Hr]; [apg H (23%bv : bv 5) 23; reflexivity|].
  destruct Hr as [<-|Hr]; [apg H (24%bv : bv 5) 24; reflexivity|].
  destruct Hr as [<-|Hr]; [apg H (25%bv : bv 5) 25; reflexivity|].
  destruct Hr as [<-|Hr]; [apg H (26%bv : bv 5) 26; reflexivity|].
  destruct Hr as [<-|Hr]; [apg H (27%bv : bv 5) 27; reflexivity|].
  destruct Hr.
Qed.

Lemma g0_kl_ap : forall (r0 r1 : bvmap 5 word), aregs_preserved r0 r1 ->
  forall r : bv 5, In r g0_kl2 -> getr r1 r = getr r0 r.
Proof.
  intros r0 r1 H r Hr. apply (ap_list r0 r1 H). unfold g0_kl2 in Hr.
  repeat (destruct Hr as [<-|Hr]; [kl_in|]). destruct Hr.
Qed.
Lemma g0_kl_sub : forall r : bv 5, In r g0_kl -> In r g0_kl2.
Proof. intros r Hr. unfold g0_kl in Hr. repeat (destruct Hr as [<-|Hr]; [kl_in|]). destruct Hr. Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation GF := (fun GI => ge_from B MT (ge_post B MT) GI).

(* The cut at the head of the loop, 0x81618, for given t, s and p: GIS_ga0's body. *)
Definition g0_inv (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (t s : Z) (p : nat) : Prop :=
  ge_body cx fp GPS_ga0 W3 ms3 GSH_a /\ k <= 2 /\ acc <= GE_A2 MT - mo_free MT /\
  gsw_blk B cx fp ly3 S3 W3 ms3 t s /\ gsw_rows cx W3 ms3 t s /\
  gslot cx W3 ms3 88 (2 ^ 64 - 1 - s) /\
  (p < 3)%nat /\
  getr (ms_regs ms3) 26 = w64 (Z.of_nat p) /\
  getr (ms_regs ms3) 25 = w64 (s + 34 + 34 * Z.of_nat p) /\
  getr (ms_regs ms3) 18 = w64 (34 + 34 * Z.of_nat p) /\
  getr (ms_regs ms3) 20 = w64 3 /\
  getr (ms_regs ms3) 27 = w64 s /\ getr (ms_regs ms3) 19 = w64 (gSH cx fp).

(* What a turn leaves at 0x81658, when check_groupa has returned: the journal grows, the
   blocks and the frames stay, the registers the loop keeps are kept, s5 holds p + 1
   (0x81628), and so is every byte the cuts name. *)
Definition g0_mid (cx : ecx) (fp k : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (t s : Z) (p : nat) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 (Z_to_bv 64 (BASE + GPS_cga0)) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(GE_CID, fp)] ly2 S2 W2 mem2 md2 k /\
    YG01.frames S2 = YG01.frames S3 /\ ablocks B ly2 S2 = ablocks B ly3 S3 /\ (exists f, S2 = set_fs f S3) /\
    (forall r : bv 5, In r g0_kl -> getr regs2 r = getr (ms_regs ms3) r) /\
    getr regs2 21 = w64 (Z.of_nat p + 1) /\
    vkeep (gsw_out cx fp t s) W3 (ms_mem ms3) W2 mem2.

Section d.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTF : ameter_fs_laws MT.
(* The two program functions a turn calls, by their own contracts. *)
Hypothesis WOF : tb_want_of_spec B.
Hypothesis TCG : tb_check_groupa_spec B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- the call of check_groupa at 0x81654 ---- *)
(* From the cut at 0x81618 to the return of check_groupa, once the walk stands at the
   call with row 1 + p in a0, a.base in a1, p in a2, the table in a3 and the value
   want_of gave in a4. *)
Lemma g0_cga_at : forall cx fp k acc ly3 S3 W3 ms3 t s (p : nat) (regsT : bvmap 5 word) memT mdT,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 memT mdT k ->
  YG01.frames S3 = [(GE_CID, fp)] ->
  g0_inv cx fp k acc ly3 S3 W3 ms3 t s p ->
  vkeep (gsw_out cx fp t s) W3 (ms_mem ms3) W3 memT ->
  (forall r : bv 5, In r g0_kl -> getr regsT r = getr (ms_regs ms3) r) ->
  getr regsT 21 = w64 (Z.of_nat p + 1) ->
  getr regsT 1 = Z_to_bv 64 (BASE + GPS_cga0) ->
  getr regsT 10 = w64 (s + 34 + 34 * Z.of_nat p) ->
  getr regsT 11 = w64 (sw_base (c_pl cx)) ->
  getr regsT 12 = w64 (Z.of_nat p) ->
  getr regsT 13 = w64 t ->
  getr regsT 14 = w64 (eff (T_end (c_pl cx)) t (sw_base (c_pl cx)) (Z.of_nat p)) ->
  SRr SEGS W3 (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA GS_check_groupa)) memT (seg_rom SEGS)) mdT)
    (g0_mid cx fp k ly3 S3 W3 ms3 t s p).
Proof.
  intros cx fp k acc ly3 S3 W3 ms3 t s p regsT memT mdT HB HJ HFR HI VK0 KR R21 R1 R10 R11 R12 R13 R14.
  destruct HI as (HBD & Hk & Hacc & HBLK & HROWS & H88 & Hp & R26 & R25 & R18 & R20 & R27 & R19).
  pose proof HBD as (_ & _ & _ & _ & _ & _ & (G2 & G8 & G9 & G3 & G4) & (S8 & S16) & _).
  pose proof HBLK as (Hab & Hins & (Hint & _) & _ & _ & _ & _ & _ & _ & _ & _ & Hok & _).
  pose proof HROWS as (Hwant & HSW).
  destruct (gsw_bounds B MT cx fp k ly3 S3 W3 memT mdT t s HB HJ HFR Hint Hins LAWS)
    as (Hal & Hsp0 & H47 & Hsp1 & Hsp32 & HF0 & HFc & HF32 & Ht0' & Htc & Hs0 & Hsc & HPB).
  (* gs_ok_range (LLVMFEntrySweepS1c.v): 0 <= a.base, 1 <= a.width, a.base + a.width <= 48 *)
  pose proof (gs_ok_range _ Hok) as (Bb0 & (Bi1 & Bi40) & Bbi).
  pose proof (sw_bytes_len cx t Hok Hwant) as Hswl.
  pose proof (length_sweep_ge (sw_base (c_pl cx)) (Z.to_nat (sw_in (c_pl cx))) (sw_vals (c_pl cx) t)) as Hsw170.
  fold (sw_bytes (c_pl cx) t) in Hsw170.
  assert (LG : forall a b c, length (GAz a b c) = 34%nat) by reflexivity.
  assert (BLKT : gsw_blk B cx fp ly3 S3 W3 (mkst regsT (Z_to_bv 64 0) memT (seg_rom SEGS)) t s)
    by exact (gsw_blk_move B cx fp ly3 S3 W3 ms3 ly3 S3 W3 (mkst regsT (Z_to_bv 64 0) memT (seg_rom SEGS)) t s
                HBLK eq_refl VK0 ltac:(lia)).
  assert (H8 : rdword (aview SEGS (w_H W3) memT) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx))).
  { eapply rdword_vkeep; [exact VK0 | | exact S8]. intros kk Hkk. left; left. lia. }
  assert (H16 : rdword (aview SEGS (w_H W3) memT) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx))).
  { pose proof (S16 0 ltac:(lia)) as Hj0.
    replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in Hj0 by lia.
    cbn [Z.ltb Z.compare] in Hj0.
    eapply rdword_vkeep; [exact VK0 | | exact Hj0]. intros kk Hkk. left; left. lia. }
  (* row 1 + p of the sweep: Pau's group-A row for a.base, p and the value the table gives *)
  assert (HROW : garr8 SEGS (mrestrict (w_H W3) memT) (s + 34 + 34 * Z.of_nat p)
                   (GAz (sw_base (c_pl cx)) (Z.of_nat p) (eff (T_end (c_pl cx)) t (sw_base (c_pl cx)) (Z.of_nat p)))).
  { replace (s + 34 + 34 * Z.of_nat p) with (s + Z.of_nat (34 * (1 + p))) by lia.
    apply (garr8_slice _ s (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)) _ (34 * (1 + p))).
    - eapply garr8_vkeep; [exact VK0 | | exact HSW]. intros a Ha. rewrite length_map in Ha. right; right. lia.
    - rewrite length_map, LG. lia.
    - intros j Hj. rewrite LG in Hj. unfold sw_bytes, sw_vals. apply sweep_row_ga0; lia. }
  assert (Q2 : getr regsT 2 = w64 (c_sp1 cx)) by (rewrite KR by kl_in; exact G2).
  assert (Q3 : getr regsT 3 = getr (c_regs cx) 3) by (rewrite KR by kl_in; exact G3).
  assert (Q4 : getr regsT 4 = getr (c_regs cx) 4) by (rewrite KR by kl_in; exact G4).
  assert (Q8 : getr regsT 8 = w64 (spZ (c_regs cx))) by (rewrite KR by kl_in; exact G8).
  eapply SRr_mono.
  { (* ch = a.base: 0 <= a.base and a.base <= 48 - a.width <= 47 (gs_ok_range);
       p < 3 from the cut; row 1 + p lies inside the sweep's 170 bytes *)
    exact (gsw_cga B MT LAWS TCG cx fp k ly3 S3 W3 regsT memT mdT GPS_cga0 t s (s + 34 + 34 * Z.of_nat p)
      (sw_base (c_pl cx)) (Z.of_nat p) HB HJ HFR BLKT Q2 Q3 Q4 Q8 R1 ltac:(unfold GPS_cga0; lia) eq_refl H8 H16
      R10 R11 R12 R13 R14 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HROW). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & Hfr2 & Hab2 & Hfs & HP & HK).
  exists ly2, S2, regs2, mem2, md2.
  split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hfr2|]. split; [exact Hab2|]. split; [exact Hfs|].
  split; [intros r Hr; rewrite (g0_kl_ap _ _ HP r (g0_kl_sub r Hr)); exact (KR r Hr)|].
  split; [apg HP (21%bv : bv 5) 21; exact R21|].
  exact (vkeep_trans _ _ _ _ _ _ _ VK0 HK).
Qed.

(* ---- one turn: 0x81618 -> the return of check_groupa at 0x81658 ---- *)
Lemma g0_turn : forall cx fp k acc ly3 S3 W3 ms3 md3 t s (p : nat),
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  YG01.frames S3 = [(GE_CID, fp)] ->
  g0_inv cx fp k acc ly3 S3 W3 ms3 t s p ->
  SRr SEGS W3 (mkCfg ms3 md3) (g0_mid cx fp k ly3 S3 W3 ms3 t s p).
Proof.
  intros cx fp k acc ly3 S3 W3 ms3 md3 t s p HB HJ HFR HI.
  pose proof HI as (HBD & Hk & Hacc & HBLK & HROWS & H88 & Hp & R26 & R25 & R18 & R20 & R27 & R19).
  pose proof HBD as (Hpc & Hrv & Hsv & Hrom & Hfr & Hfc & (G2 & G8 & G9 & G3 & G4) & (S8 & S16) & HSH & _).
  pose proof HBLK as (Hab & Hins & (Hint & Ht0 & _) & _ & _ & HREL & _ & HSL & _ & _ & _ & Hok & A0 & A1).
  destruct HSL as (L8 & L16 & L40 & L48 & L56 & L64 & L72 & L80 & L96 & L104 & L112 & L120 & L128 & L136 & L144 & L152).
  pose proof HROWS as (Hwant & HSW).
  (* gs_ok_range (LLVMFEntrySweepS1c.v): 0 <= a.base, 1 <= a.width, a.base + a.width <= 48 *)
  pose proof (gs_ok_range _ Hok) as (Bb0 & (Bi1 & Bi40) & Bbi).
  destruct (gsw_bounds B MT cx fp k ly3 S3 W3 (ms_mem ms3) md3 t s HB HJ HFR Hint Hins LAWS)
    as (Hal & Hsp0 & H47 & Hsp1 & Hsp32 & HF0 & HFc & HF32 & Ht0' & Htc & Hs0 & Hsc & HPB).
  pose proof (@alloc_ceiling_value rc) as HAC. unfold GE_STK, STK_LLVMFuzzerTestOneInput in Hsp0.
  pose proof (sw_mbytes_ge (c_pl cx)) as Hsm.
  pose proof (g0_seat cx fp t s W3 (ms_regs ms3) (ms_mem ms3) GPS_ga0 G9 ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(unfold GO_A; lia) H88 L120 L128 L136 L152 A0 A1) as HS.
  remember (g0_mid cx fp k ly3 S3 W3 ms3 t s p) as Q eqn:HQ.
  rewrite (ms_shape ms3 (BASE + GPS_ga0) Hpc Hrv Hsv Hrom Hfr Hfc).
  remember (Eg (ms_regs ms3) (g0_xs cx fp t s)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg (ms_regs ms3) (map (Z_to_bv 64) (g0_xs cx fp t s))) E)
    by (subst E; apply env_agree_Eimg).
  assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r)
    by (intros n r Hn; subst E; apply Eg_reg; exact Hn).
  assert (E32 : ew E 32 = Z_to_bv 64 (2 ^ 64 - 1 - s)) by (subst E; exact (Eg_x _ _ 0 ltac:(cbv; lia))).
  assert (E34 : ew E 34 = Z_to_bv 64 (gF cx fp + GO_SET)) by (subst E; exact (Eg_x _ _ 2 ltac:(cbv; lia))).
  assert (E35 : ew E 35 = Z_to_bv 64 (gF cx fp + GO_WAS)) by (subst E; exact (Eg_x _ _ 3 ltac:(cbv; lia))).
  assert (E36 : ew E 36 = Z_to_bv 64 (sw_base (c_pl cx))) by (subst E; exact (Eg_x _ _ 4 ltac:(cbv; lia))).
  assert (E18 : ew E 18 = Z_to_bv 64 (34 + 34 * Z.of_nat p)) by (rewrite (ER 18%nat 18%bv eq_refl); exact R18).
  assert (E26 : ew E 26 = Z_to_bv 64 (Z.of_nat p)) by (rewrite (ER 26%nat 26%bv eq_refl); exact R26).
  clear HE.
  assert (SHOK : sh_ok SEGS Bx3 [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  (* run 1: 0x81618 -> `bltu a0,s2` at 0x8161c; a0 is slot 88 *)
  paj_run_tok RUN HS HJ SHOK Bsp3; [g0_awr|].
  g0_mem HM1.
  psrr_branch_tok RUN BR HS SHOK Bsp3.
  { (* 0x8161c into the UBSan trap 0x81f48: taken only if 2^64 - 1 - s <u 34 + 34p,
       but s lies below the allocator's ceiling and 34 + 34p <= 102 *)
    exfalso. rewrite branch_ltu_U, (U_atom E 32 _ E32), (U_atom E 18 _ E18) in Hc by lia.
    apply Z.ltb_lt in Hc. lia. }
  clear Hc.
  (* run 1, continued: 0x81620 -> the call of want_of at 0x8163c *)
  paj_run_tok RUN HS HJ SHOK Bsp3; [g0_awr|].
  g0_mem HM2.
  lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msW end.
  pose proof (regs_kept_of_st_ok SEGS _ _ _ (ms_regs ms3) _ g0_kl HS HAE ltac:(vm_compute; reflexivity)) as KF.
  cbn [ms_regs restrict] in KF.
  prreg HS (1%bv : bv 5) Ra. prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1.
  prreg HS (12%bv : bv 5) Ra2. prreg HS (13%bv : bv 5) Ra3.
  prreg HS (21%bv : bv 5) Ra21. prreg HS (24%bv : bv 5) Ra24.
  pmkst HS.
  (* `addi s5,s10,1` at 0x81628 and `lbu s8,0(a0)` at 0x81624 *)
  assert (Q21 : getr (ms_regs msW) 21 = w64 (Z.of_nat p + 1)) by zreg Ra21 E26.
  assert (Q24 : getr (ms_regs msW) 24 = w64 (sw_base (c_pl cx))) by zreg Ra24 E36.
  assert (VKW : vkeep (gsw_out cx fp t s) W3 (ms_mem ms3) W3 (ms_mem msW))
    by (apply vkeep_mem; intros x; rewrite HM2, HM1; reflexivity).
  eapply SRr_bind.
  { apply (gsw_want B MT LAWS WOF cx fp k ly3 S3 W3 (ms_regs msW) (ms_mem msW) _ GPS_want0 t s
      (sw_base (c_pl cx)) (Z.of_nat p) HB HJ HFR).
    - exact (gsw_blk_move B cx fp ly3 S3 W3 ms3 ly3 S3 W3 (mkst (ms_regs msW) (Z_to_bv 64 0) (ms_mem msW) (seg_rom SEGS))
        t s HBLK eq_refl VKW ltac:(lia)).
    - intros i Hi. rewrite HM2, HM1. exact (HSH i Hi).
    - rewrite KF by kl_in. exact G2.
    - rewrite KF by kl_in. exact G3.
    - rewrite KF by kl_in. exact G4.
    - rewrite KF by kl_in. exact G8.
    - rewrite Ra. reflexivity.
    - unfold GPS_want0. lia.
    - reflexivity.
    - rewrite HM2, HM1. exact S8.
    - rewrite HM2, HM1. pose proof (S16 0 ltac:(lia)) as Hj0.
      replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in Hj0 by lia.
      cbn [Z.ltb Z.compare] in Hj0. exact Hj0.
    - (* `ld a0,136(s1)`: was_set *) zreg Ra0 E35.
    - (* `ld a1,128(s1)`: set_to *) zreg Ra1 E34.
    - (* `mv a2,s8`: c = a.base *) zreg Ra2 E36.
    - (* `mv a3,s10`: p *) zreg Ra3 E26.
    - (* THE c DISCHARGE: c = a.base, the byte `lbu s8,0(a0)` read at 0x81624 from slot 120's
         address; gsw_blk's `ok` gives 0 <= a.base and a.base + a.width <= 48 with
         1 <= a.width (gs_ok_range), so 0 <= c <= 47. *)
      lia.
    - (* THE p DISCHARGE: p = s10 at the cut, and the cut carries (p < 3)%nat (the back
         edge `bne s5,s4` at 0x81664 with s4 = 3 keeps it). *)
      lia. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HK2 & H10).
  clear HS SHOK Ra Ra0 Ra1 Ra2 Ra3 Ra21 Ra24.
  (* run 2: 0x81640 -> the call of check_groupa at 0x81654; the seat reads the cut's bytes
     through the call *)
  assert (VK1 : vkeep (gsw_out cx fp t s) W3 (ms_mem ms3) W3 mem2) by exact (vkeep_trans _ _ _ _ _ _ _ VKW HK2).
  assert (KS : forall off v, 8 <= off <= 152 -> rdword (aview SEGS (w_H W3) (ms_mem ms3)) (c_sp1 cx + off) = Some v ->
             rdword (aview SEGS (w_H W3) mem2) (c_sp1 cx + off) = Some v).
  { intros off v Hoff Hr. eapply rdword_vkeep; [exact VK1 | | exact Hr]. intros kk Hkk. left; left. lia. }
  assert (KA : forall off v, 0 <= off < 1024 -> aview SEGS (w_H W3) (ms_mem ms3) (gF cx fp + off) = Some v ->
             aview SEGS (w_H W3) mem2 (gF cx fp + off) = Some v).
  { intros off v Hoff Hr. rewrite (VK1 (gF cx fp + off)); [exact Hr | left; right; right; left; lia]. }
  assert (R9b : getr regs2 9 = w64 (c_sp1 cx)) by (apg HP2 (9%bv : bv 5) 9; rewrite KF by kl_in; exact G9).
  pose proof (g0_seat cx fp t s W3 regs2 mem2 GPS_want0 R9b ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(unfold GO_A; lia) (KS 88 _ ltac:(lia) H88) (KS 120 _ ltac:(lia) L120) (KS 128 _ ltac:(lia) L128)
    (KS 136 _ ltac:(lia) L136) (KS 152 _ ltac:(lia) L152) (KA GO_A _ ltac:(unfold GO_A; lia) A0)
    (KA (GO_A + 1) _ ltac:(unfold GO_A; lia) A1)) as HS2.
  remember (Eg regs2 (g0_xs cx fp t s)) as E2 eqn:HE2.
  assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
  assert (HAE2 : env_agree 32 (Ereg regs2 (map (Z_to_bv 64) (g0_xs cx fp t s))) E2)
    by (subst E2; apply env_agree_Eimg).
  assert (ER2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs2 r)
    by (intros n r Hn; subst E2; apply Eg_reg; exact Hn).
  assert (F38 : ew E2 38 = Z_to_bv 64 t) by (subst E2; exact (Eg_x _ _ 6 ltac:(cbv; lia))).
  clear HE2.
  assert (SHOK2 : sh_ok SEGS Bx3 [] E2 (mrestrict (w_H W3) mem2)) by constructor.
  paj_run_tok RUN HS2 HJ2 SHOK2 Bsp3; [g0_awr|].
  g0_mem HM3.
  lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msC end.
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regs2 _ g0_kl2 HS2 HAE2 ltac:(vm_compute; reflexivity)) as KF2.
  cbn [ms_regs restrict] in KF2.
  prreg HS2 (1%bv : bv 5) Rb. prreg HS2 (10%bv : bv 5) Rb0. prreg HS2 (11%bv : bv 5) Rb1.
  prreg HS2 (12%bv : bv 5) Rb2. prreg HS2 (13%bv : bv 5) Rb3. prreg HS2 (14%bv : bv 5) Rb4.
  pmkst HS2. subst Q.
  (* the registers callee-saved through want_of and kept by both runs *)
  assert (KC : forall r : bv 5, In r g0_kl2 -> getr (ms_regs msC) r = getr (ms_regs msW) r).
  { intros r Hr. rewrite (KF2 r Hr). exact (g0_kl_ap _ _ HP2 r Hr). }
  apply (g0_cga_at cx fp k acc ly3 S3 W3 ms3 t s p (ms_regs msC) (ms_mem msC) _ HB HJ2 HFR HI).
  - rewrite HM3. exact VK1.
  - intros r Hr. rewrite (KC r (g0_kl_sub r Hr)). exact (KF r Hr).
  - rewrite (KC 21%bv) by kl_in. exact Q21.
  - rewrite Rb. reflexivity.
  - (* `mv a0,s9`: the row *)
    rewrite Rb0, (ER2 25%nat 25%bv eq_refl). apg HP2 (25%bv : bv 5) 25. rewrite KF by kl_in. exact R25.
  - (* `mv a1,s8`: a.base *)
    rewrite Rb1, (ER2 24%nat 24%bv eq_refl). apg HP2 (24%bv : bv 5) 24. exact Q24.
  - (* `mv a2,s10`: p *)
    rewrite Rb2, (ER2 26%nat 26%bv eq_refl). apg HP2 (26%bv : bv 5) 26. rewrite KF by kl_in. exact R26.
  - (* `ld a3,152(s1)`: the table *) zreg Rb3 F38.
  - (* `mv a4,a0`: the value want_of gave *)
    rewrite Rb4, (ER2 10%nat 10%bv eq_refl). exact H10.
Qed.

Section e.
Hypothesis NEXT1 : GF (GIS_ga1 B MT).
Hypothesis NEXT2 : GF (GIS_gbhd B MT).

(* ---- after check_groupa: 0x81658 -> 0x81618, 0x81684 or 0x8173c ---- *)
Lemma g0_tail : forall cx fp k acc ly3 S3 W3 ms3 md3 t s (p : nat) (W2 : world SEGS) (c2 : config),
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  YG01.frames S3 = [(GE_CID, fp)] ->
  mo_le MT (c_S cx) S3 acc ->
  g0_inv cx fp k acc ly3 S3 W3 ms3 t s p ->
  ((S p < 3)%nat -> forall ly4 S4 W4 (ms4 : machine_state) md4,
     ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
       [(GE_CID, fp)] ly4 S4 W4 (ms_mem ms4) md4 k ->
     YG01.frames S4 = [(GE_CID, fp)] -> mo_le MT (c_S cx) S4 acc ->
     g0_inv cx fp k acc ly4 S4 W4 ms4 t s (S p) -> SRr SEGS W4 (mkCfg ms4 md4) (ge_post B MT cx)) ->
  g0_mid cx fp k ly3 S3 W3 ms3 t s p W2 c2 ->
  SRr SEGS W2 c2 (ge_post B MT cx).
Proof.
  intros cx fp k acc ly3 S3 W3 ms3 md3 t s p W2 c2 HB HJ HFR Hmo HI IH HM.
  destruct HM as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & Hfr2 & Hab2 & (f & ES2) & KR & R21 & VK).
  pose proof HI as (HBD & Hk & Hacc & HBLK & HROWS & H88 & Hp & R26 & R25 & R18 & R20 & R27 & R19).
  pose proof HBD as (Hpc & Hrv & Hsv & Hrom & Hfr & Hfc & (G2 & G8 & G9 & G3 & G4) & _).
  pose proof HBLK as (Hab & Hins & (Hint & Ht0 & _) & _ & _ & _ & _ & HSL & _ & _ & _ & Hok & A0 & A1).
  destruct HSL as (L8 & L16 & L40 & L48 & L56 & L64 & L72 & L80 & L96 & L104 & L112 & L120 & L128 & L136 & L144 & L152).
  pose proof HROWS as (Hwant & HSW).
  pose proof (gs_ok_range _ Hok) as (Bb0 & (Bi1 & Bi40) & Bbi).
  destruct (gsw_bounds B MT cx fp k ly3 S3 W3 (ms_mem ms3) md3 t s HB HJ HFR Hint Hins LAWS)
    as (Hal & Hsp0 & H47 & Hsp1 & Hsp32 & HF0 & HFc & HF32 & Ht0' & Htc & Hs0 & Hsc & HPB).
  pose proof (@alloc_ceiling_value rc) as HAC. unfold GE_STK, STK_LLVMFuzzerTestOneInput in Hsp0.
  pose proof (sw_mbytes_ge (c_pl cx)) as Hsm.
  assert (HFR2 : YG01.frames S2 = [(GE_CID, fp)]) by (rewrite Hfr2; exact HFR).
  assert (Hmo2 : mo_le MT (c_S cx) S2 acc) by (rewrite ES2; apply (mo_le_set_fs_r MT MTF); exact Hmo).
  (* the cut's bytes, through the two calls *)
  assert (KS : forall off v, 8 <= off <= 152 -> rdword (aview SEGS (w_H W3) (ms_mem ms3)) (c_sp1 cx + off) = Some v ->
             rdword (aview SEGS (w_H W2) mem2) (c_sp1 cx + off) = Some v).
  { intros off v Hoff Hr. eapply rdword_vkeep; [exact VK | | exact Hr]. intros kk Hkk. left; left. lia. }
  assert (KA : forall off v, 0 <= off < 1024 -> aview SEGS (w_H W3) (ms_mem ms3) (gF cx fp + off) = Some v ->
             aview SEGS (w_H W2) mem2 (gF cx fp + off) = Some v).
  { intros off v Hoff Hr. rewrite (VK (gF cx fp + off)); [exact Hr | left; right; right; left; lia]. }
  assert (R9' : getr regs2 9 = w64 (c_sp1 cx)) by (rewrite KR by kl_in; exact G9).
  pose proof (g0_seat cx fp t s W2 regs2 mem2 GPS_cga0 R9' ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(unfold GO_A; lia) (KS 88 _ ltac:(lia) H88) (KS 120 _ ltac:(lia) L120) (KS 128 _ ltac:(lia) L128)
    (KS 136 _ ltac:(lia) L136) (KS 152 _ ltac:(lia) L152) (KA GO_A _ ltac:(unfold GO_A; lia) A0)
    (KA (GO_A + 1) _ ltac:(unfold GO_A; lia) A1)) as HS.
  remember (Eg regs2 (g0_xs cx fp t s)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs2 (map (Z_to_bv 64) (g0_xs cx fp t s))) E)
    by (subst E; apply env_agree_Eimg).
  assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
    by (intros n r Hn; subst E; apply Eg_reg; exact Hn).
  assert (E37 : ew E 37 = Z_to_bv 64 (sw_in (c_pl cx))) by (subst E; exact (Eg_x _ _ 5 ltac:(cbv; lia))).
  clear HE.
  assert (EK : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> In r g0_kl -> ew E n = getr (ms_regs ms3) r)
    by (intros n r Hn Hr; rewrite (ER n r Hn); exact (KR r Hr)).
  assert (E21 : ew E 21 = Z_to_bv 64 (Z.of_nat p + 1)) by (rewrite (ER 21%nat 21%bv eq_refl); exact R21).
  assert (E20 : ew E 20 = Z_to_bv 64 3) by (rewrite (EK 20%nat 20%bv eq_refl) by kl_in; exact R20).
  assert (E25 : ew E 25 = Z_to_bv 64 (s + 34 + 34 * Z.of_nat p)) by (rewrite (EK 25%nat 25%bv eq_refl) by kl_in; exact R25).
  assert (E18 : ew E 18 = Z_to_bv 64 (34 + 34 * Z.of_nat p)) by (rewrite (EK 18%nat 18%bv eq_refl) by kl_in; exact R18).
  assert (E27 : ew E 27 = Z_to_bv 64 s) by (rewrite (EK 27%nat 27%bv eq_refl) by kl_in; exact R27).
  assert (SHOK : sh_ok SEGS Bx3 [] E (mrestrict (w_H W2) mem2)) by constructor.
  (* run 1: 0x81658 -> `bne s5,s4` at 0x81664 *)
  paj_run_tok RUN HS HJ2 SHOK Bsp3; [g0_awr|].
  g0_mem HM1.
  psrr_branch_tok RUN BR HS SHOK Bsp3.
  - (* p + 1 <> 3: back to the head 0x81618 with p + 1 *)
    rewrite branch_ne_U, (U_atom E 21 (Z.of_nat p + 1) E21), (U_atom E 20 3 E20) in Hc by lia.
    apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ2 SHOK Bsp3 GPS_ga0; [g0_awr|].
    g0_mem HM2.
    lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msF end.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 _ g0_kl1 HS HAE ltac:(vm_compute; reflexivity)) as KF.
    cbn [ms_regs restrict] in KF.
    assert (KRF : forall r : bv 5, In r g0_kl1 -> getr (ms_regs msF) r = getr (ms_regs ms3) r).
    { intros r Hr. rewrite (KF r Hr). apply KR. unfold g0_kl1 in Hr.
      repeat (destruct Hr as [<-|Hr]; [kl_in|]). destruct Hr. }
    prreg HS (26%bv : bv 5) Q26. prreg HS (25%bv : bv 5) Q25. prreg HS (18%bv : bv 5) Q18.
    pmkst HS.
    assert (VKF : vkeep (gsw_out cx fp t s) W3 (ms_mem ms3) W2 (ms_mem msF)) by (rewrite HM2, HM1; exact VK).
    eapply (IH ltac:(lia)); [exact HJ2 | exact HFR2 | exact Hmo2 |].
    split.
    { apply (ge_body_move cx fp GPS_ga0 GPS_ga0 W3 W2 ms3 (ms_regs msF) (ms_mem msF) GSH_a HBD).
      - eapply vkeep_sub; [| exact VKF]. intros a Ha. left. exact Ha.
      - lia.
      - apply KRF. kl_in.
      - apply KRF. kl_in.
      - apply KRF. kl_in.
      - apply KRF. kl_in.
      - apply KRF. kl_in. }
    split; [exact Hk|]. split; [exact Hacc|].
    split; [eapply gsw_blk_move; [exact HBLK | exact Hab2 | exact VKF | lia]|].
    split; [eapply gsw_rows_move; [exact Hok | exact HROWS | exact VKF]|].
    split; [unfold gslot; eapply rdword_vkeep; [exact VKF | | exact H88]; intros kk Hkk; left; left; lia|].
    split; [lia|].
    cbn [ms_regs mkst].
    (* `mv s10,s5`, `addi s9,s9,34`, `addi s2,s2,34` at 0x81660, 0x81658, 0x8165c *)
    split; [zreg Q26 E21|].
    split; [zreg Q25 E25|].
    split; [zreg Q18 E18|].
    split; [rewrite KRF by kl_in; exact R20|].
    split; [rewrite KRF by kl_in; exact R27|].
    rewrite KRF by kl_in. exact R19.
  - (* p + 1 = 3: the loop is done; `bltu a0,a1` at 0x81674 tests a.width < 2 *)
    clear Hc.
    paj_run_tok RUN HS HJ2 SHOK Bsp3; [g0_awr|].
    g0_mem HM2.
    psrr_branch_tok RUN BR HS SHOK Bsp3.
    + (* a.width < 2: 0x8171c .. 0x81738, on to group B, 0x8173c with i = 0 *)
      rewrite branch_ltu_U, (U_zext8 E 37 _ E37), U_lit in Hc by lia.
      apply Z.ltb_lt in Hc.
      paj_run_to_tok RUNTO HS HJ2 SHOK Bsp3 GPS_gbhd; [g0_awr|].
      g0_mem HM3.
      lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msG end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 _ [2; 3; 4; 8; 9; 19; 27]%bv HS HAE
        ltac:(vm_compute; reflexivity)) as KF.
      cbn [ms_regs restrict] in KF.
      assert (KRG : forall r : bv 5, In r [2; 3; 4; 8; 9; 19; 27]%bv -> getr (ms_regs msG) r = getr (ms_regs ms3) r).
      { intros r Hr. rewrite (KF r Hr). apply KR.
        repeat (destruct Hr as [<-|Hr]; [kl_in|]). destruct Hr. }
      prreg HS (18%bv : bv 5) Q18. prreg HS (24%bv : bv 5) Q24. prreg HS (20%bv : bv 5) Q20.
      prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (21%bv : bv 5) Q21.
      prreg HS (25%bv : bv 5) Q25.
      pmkst HS.
      assert (VKG : vkeep (gsw_out cx fp t s) W3 (ms_mem ms3) W2 (ms_mem msG))
        by (rewrite HM3, HM2, HM1; exact VK).
      eapply NEXT2; [exact HB | exact HJ2 | exact HFR2 | exact Hmo2 |].
      exists t, s, 0%nat.
      split.
      { apply (ge_body_move cx fp GPS_ga0 GPS_gbhd W3 W2 ms3 (ms_regs msG) (ms_mem msG) GSH_a HBD).
        - eapply vkeep_sub; [| exact VKG]. intros a Ha. left. exact Ha.
        - lia.
        - apply KRG. kl_in.
        - apply KRG. kl_in.
        - apply KRG. kl_in.
        - apply KRG. kl_in.
        - apply KRG. kl_in. }
      split; [exact Hk|]. split; [exact Hacc|].
      split; [eapply gsw_blk_move; [exact HBLK | exact Hab2 | exact VKG | lia]|].
      split; [eapply gsw_rows_move; [exact Hok | exact HROWS | exact VKG]|].
      split; [unfold gslot; eapply rdword_vkeep; [exact VKG | | exact H88]; intros kk Hkk; left; left; lia|].
      split; [lia|].
      cbn [ms_regs mkst].
      (* `mv s2,zero`, `mv s8,zero`, `addi s4,s11,170`, `addi s6,s11,190`, `addi s7,s11,186`,
         `li s5,-8` and the auipc/addi pair 0x81730/0x81738 of POLL (object 6) *)
      split; [zreg Q18 E27|].
      split; [zreg Q24 E27|].
      split; [zreg Q20 E27|].
      split; [zreg Q22 E27|].
      split; [zreg Q23 E27|].
      split; [zreg Q21 E27|].
      split; [rewrite Q25, (img_env_atomP E _ HEI) by (unfold A_TEXT, A_LIM; lia); apply zeq64;
              change (A_OBJ 6) with 247%nat; lia|].
      split; [rewrite KRG by kl_in; exact R27|].
      rewrite KRG by kl_in. exact R19.
    + (* a.width >= 2: 0x81678 .. 0x81680, on to group A for the channels 1 .. w-1, 0x81684 with c = 1 *)
      rewrite branch_ltu_U, (U_zext8 E 37 _ E37), U_lit in Hc by lia.
      apply Z.ltb_ge in Hc.
      paj_run_to_tok RUNTO HS HJ2 SHOK Bsp3 GPS_ga1; [g0_awr|].
      g0_mem HM3.
      lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msG end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 _ g0_kl1 HS HAE ltac:(vm_compute; reflexivity)) as KF.
      cbn [ms_regs restrict] in KF.
      assert (KRG : forall r : bv 5, In r g0_kl1 -> getr (ms_regs msG) r = getr (ms_regs ms3) r).
      { intros r Hr. rewrite (KF r Hr). apply KR. unfold g0_kl1 in Hr.
        repeat (destruct Hr as [<-|Hr]; [kl_in|]). destruct Hr. }
      prreg HS (18%bv : bv 5) Q18. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
      pmkst HS.
      assert (VKG : vkeep (gsw_out cx fp t s) W3 (ms_mem ms3) W2 (ms_mem msG))
        by (rewrite HM3, HM2, HM1; exact VK).
      eapply NEXT1; [exact HB | exact HJ2 | exact HFR2 | exact Hmo2 |].
      exists t, s, 1%nat.
      split.
      { apply (ge_body_move cx fp GPS_ga0 GPS_ga1 W3 W2 ms3 (ms_regs msG) (ms_mem msG) GSH_a HBD).
        - eapply vkeep_sub; [| exact VKG]. intros a Ha. left. exact Ha.
        - lia.
        - apply KRG. kl_in.
        - apply KRG. kl_in.
        - apply KRG. kl_in.
        - apply KRG. kl_in.
        - apply KRG. kl_in. }
      split; [exact Hk|]. split; [exact Hacc|].
      split; [eapply gsw_blk_move; [exact HBLK | exact Hab2 | exact VKG | lia]|].
      split; [eapply gsw_rows_move; [exact Hok | exact HROWS | exact VKG]|].
      split; [unfold gslot; eapply rdword_vkeep; [exact VKG | | exact H88]; intros kk Hkk; left; left; lia|].
      split; [lia|]. split; [lia|].
      cbn [ms_regs mkst].
      (* `li s2,1`, `li s5,34`, `li s6,3` at 0x81678 .. 0x81680 *)
      split; [zreg Q18 E27|].
      split; [zreg Q21 E27|].
      split; [zreg Q22 E27|].
      split; [rewrite KRG by kl_in; exact R27|].
      rewrite KRG by kl_in. exact R19.
Qed.

(* ---- the loop, by induction on the turns left (3 - p) ---- *)
Lemma g0_loop : forall (n : nat) cx fp k acc ly3 S3 W3 ms3 md3 t s (p : nat),
  (3 - p = n)%nat ->
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  YG01.frames S3 = [(GE_CID, fp)] ->
  mo_le MT (c_S cx) S3 acc ->
  g0_inv cx fp k acc ly3 S3 W3 ms3 t s p ->
  SRr SEGS W3 (mkCfg ms3 md3) (ge_post B MT cx).
Proof.
  induction n as [|n IHn]; intros cx fp k acc ly3 S3 W3 ms3 md3 t s p Hn HB HJ HFR Hmo HI.
  - exfalso. destruct HI as (_ & _ & _ & _ & _ & _ & Hp & _). lia.
  - eapply SRr_bind; [exact (g0_turn cx fp k acc ly3 S3 W3 ms3 md3 t s p HB HJ HFR HI)|].
    intros W2 c2 _ HM.
    apply (g0_tail cx fp k acc ly3 S3 W3 ms3 md3 t s p W2 c2 HB HJ HFR Hmo HI); [|exact HM].
    intros Hp1 ly4 S4 W4 ms4 md4 HJ4 HFR4 Hmo4 HI4.
    exact (IHn cx fp k acc ly4 S4 W4 ms4 md4 t s (S p) ltac:(lia) HB HJ4 HFR4 Hmo4 HI4).
Qed.

Lemma g0_seg : GF (GIS_ga0 B MT).
Proof.
  intros cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR Hmo HI.
  destruct HI as (t & s & p & HI).
  exact (g0_loop (3 - p) cx fp k acc ly3 S3 W3 ms3 md3 t s p eq_refl HB HJ HFR Hmo HI).
Qed.

End e.
End d.
End c.
End b.
End a.

Section z. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section zb.
Context {PI : PAImg grant_listing}.

(* 0x81618 -> 0x81684 or 0x8173c: the first group-A loop, from the contracts of want_of
   and check_groupa (GrantBContracts.v tb_want_of_spec, tb_check_groupa_spec). *)
Lemma gsw_seg_ga0 : forall (B : asyms) (MT : ameter_ops),
  GrantBContracts.tb_want_of_spec B -> GrantBContracts.tb_check_groupa_spec B -> @SEG_ga0 fx rc SK PI B MT.
Proof.
  intros B MT WOF TCG RT NEXT1 NEXT2.
  destruct RT as (LAWS & TL & TLF & ML & MTL & MTF & AMALLOC4 & AFREE4 & ABCMP & HVIS & HGL & RO).
  exact (g0_seg B MT LAWS MTF WOF TCG NEXT1 NEXT2).
Qed.

End zb.
End z.
