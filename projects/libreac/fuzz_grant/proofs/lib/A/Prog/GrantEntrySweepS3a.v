(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySweepS3b), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8v.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySweepS3b.v, with its numbers changed; 765 of its 923 lines of code are new or changed and 1036 lines of the source are left out. *)
(* Segment 3, part a, of the sweep phase: 0x8103c -> 0x81104 or 0x811f8 — the first
   group-A loop (fuzz_grant.c:325-327): for p = 0, 1, 2 the harness reads
   was_set[3 * a.base + p], takes set_to[...] or reac_headamp_default(p) as the value
   it wants, and calls check_groupa on sweep row 1 + p. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YC5d YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaJournal GrantSyms GrantList GrantPa GrantPaLib GrantBase GrantRo GrantEntryDefs GrantEntrySweepDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
GrantFrame YC1g YC1h YC1i YC88 YC85 GrantEntrySweepS3c GrantEntrySweepS3d HeadampTxEffective HeadampDefault CheckGroupa.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel GrantModel GrantSweepModel BuildSweepModel SweepRowCheck GrantSlotPlan.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require SlotNeeds_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ---- the model facts of one turn ---- *)
Lemma ok_bounds : forall pl, ok pl = true ->
  0 <= sw_base pl /\ 1 <= sw_in pl /\ sw_in pl <= 40 /\ sw_base pl + sw_in pl <= 48.
Proof.
  intros pl H. unfold ok, fits in H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1, H2, H3, H4. unfold sw_base, sw_in. lia.
Qed.

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

(* The value the harness wants for (ch, p) is the table's effective value
   (GrantSlotPlan.v Hrel, HeadampModel.v eff_cell). *)
Lemma want_eff : forall pl t ch (p : nat), 0 <= ch < 48 -> 0 < t -> (p < 3)%nat ->
  Hrel (T_end pl) (ws_end pl) (st_end pl) ->
  eff (T_end pl) t ch (Z.of_nat p) =
  if tb (ws_end pl) (3 * ch + Z.of_nat p) =? 0 then dflt (Z.of_nat p)
  else tb (st_end pl) (3 * ch + Z.of_nat p).
Proof.
  intros pl t ch p Hch Ht Hp HR.
  rewrite eff_cell by lia.
  destruct (HR ch (Z.of_nat p) ltac:(lia) ltac:(lia)) as [H1 H2].
  rewrite H1, H2. reflexivity.
Qed.

Lemma GSH_a_zero : forall k, (4 <= k < 22)%nat \/ (30 <= k < 48)%nat -> nth k GSH_a 0 = 0.
Proof.
  intros k Hk. assert (Hk' : (k < 48)%nat) by lia.
  do 48 (destruct k as [|k]; [first [reflexivity | lia] |]). lia.
Qed.

(* ---- the symbolic state at the head of the loop, 0x8103c ---- *)
(* Atoms: 32 a.base, 33 a.in, 34..37 the spill slots 8, 64, 136, 144, 38/39 the
   address and value of was_set[3 * a.base + p], 40/41 the same for set_to, 42/43 the
   shadow bytes of those two entries. *)
Definition GPS_hdef : Z := 0x9e4.   (* 0x81094, after reac_headamp_default *)
Definition GPS_cga0 : Z := 0x9fc.   (* 0x810ac, after check_groupa         *)
Definition OFF0 : sv := SAlu ALU_ADD (SOff 26 0) (SAlu ALU_ADD (SAlu ALU_SLL (SOff 32 0) (SLit 1)) (SOff 32 0)).
Definition g0_alias : list (sv * sv) :=
  [ (SAlu ALU_ADD (SOff 37 0) OFF0, SOff 38 0);
    (SAlu ALU_ADD (SAlu ALU_SRL (SOff 38 0) (SLit 3)) (SLit SB3), SOff 42 0);
    (SAlu ALU_ADD (SOff 36 0) OFF0, SOff 40 0);
    (SAlu ALU_ADD (SAlu ALU_SRL (SOff 40 0) (SLit 3)) (SLit SB3), SOff 43 0) ].
Definition g0_atoms : list (nat * afact) :=
  [ (26%nat, mkAF 0 2 0); (32%nat, mkAF 0 47 0); (33%nat, mkAF 0 255 0);
    (39%nat, mkAF 0 255 0); (41%nat, mkAF 0 255 0) ].
Definition RA3 : YP09.region :=
  YP09.mkRegion (Some 18%nat) 0 2 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0)); YP09.mkChunk 1 (CVal 1 (SOff 33 0))].
Definition RS3 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 8 160 0 0
    [YP09.mkChunk 8 (CVal 8 (SOff 34 0)); YP09.mkChunk 64 (CVal 8 (SOff 35 0));
     YP09.mkChunk 136 (CVal 8 (SOff 36 0)); YP09.mkChunk 144 (CVal 8 (SOff 37 0));
     YP09.mkChunk 152 (CVal 8 (SLit SB3))].
Definition R1b (n v : nat) : YP09.region := YP09.mkRegion (Some n) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff v 0))].
Definition R1z (n : nat) : YP09.region := YP09.mkRegion (Some n) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition g0_regions : YP09.smem := [RA3; RS3; R1b 38 39; R1z 42; R1b 40 41; R1z 43].
Definition ss_g0 : sstate :=
  mkSS GPS_ga0 (sr_set sr_atoms 23%bv (SLit SB3)) g0_regions None (mkFacts g0_atoms [] g0_alias).
(* After check_groupa: the loop's test and, on the way out, a.in and two spill slots. *)
Definition ss_g0x : sstate := mkSS GPS_cga0 sr_atoms [RA3; RS3] None (mkFacts [(33%nat, mkAF 0 255 0)] [] []).

Definition g0_i (pl : list byte) (p : Z) : Z := 3 * sw_base pl + p.

(* The registers a turn keeps from the head of the loop to the return of check_groupa. *)
Definition g0_kl : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 26; 27]%bv.
(* The same less s7, which the symbolic state at the head pins to the shadow offset. *)
Definition g0_kl0 : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 26; 27]%bv.
(* The registers the runs after check_groupa leave as they found them. *)
Definition g0_kl1 : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23]%bv.
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
(* The memory a run over read-only regions leaves: the one it started from. *)
Ltac g0_mem HM :=
  lazymatch goal with HFx : frame_of _ ?rs ?m (ms_mem ?msn) |- _ =>
    pose proof (frame_of_read_only _ rs m (ms_mem msn) ltac:(vm_compute; reflexivity) HFx) as HM end;
  cbn [ms_mem mkst] in HM;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* The kept registers at a stop of the first run: g0_kl0 from the engine, s7 from its pin. *)
Ltac kl_cases KF H23 R23 :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; unfold g0_kl in Hr;
  repeat (destruct Hr as [<-|Hr]; [first [ apply KF; kl_in | rewrite H23, R23; reflexivity ] |]);
  destruct Hr.

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

Definition g0_xs (cx : ecx) (fp s p : Z) : list Z :=
  let pl := c_pl cx in let i := g0_i pl p in
  [ sw_base pl; sw_in pl; gF cx fp + GO_POLL; s; gF cx fp + GO_SET; gF cx fp + GO_WAS;
    gF cx fp + GO_WAS + i; tb (ws_end pl) i; gF cx fp + GO_SET + i; tb (st_end pl) i;
    SHADOW_OFF + gF cx fp / 8 + (GO_WAS + i) / 8; SHADOW_OFF + gF cx fp / 8 + (GO_SET + i) / 8 ].

Lemma Eg_reg : forall (regs : bvmap 5 word) xs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eg regs xs) n = getr regs r.
Proof. intros regs xs n r Hn. unfold Eg. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma Eg_x : forall (regs : bvmap 5 word) xs j, (32 + j < A_TEXT)%nat -> ew (Eg regs xs) (32 + j) = Z_to_bv 64 (nth j xs 0).
Proof.
  intros regs xs j Hj. unfold Eg. rewrite Eimg_low by exact Hj. rewrite ew_Ereg_extra.
  exact (map_nth (Z_to_bv 64) xs 0 j).
Qed.
Lemma VB : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v.
Proof. intros E n v H Hv. cbn [base_val]. rewrite H. apply unsigned_lit_small. exact Hv. Qed.
Lemma sv_SOff0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

(* The value of OFF0-based addresses: A + 3 * base + p. *)
Lemma denot_off0 : forall E n A b p, ew E n = Z_to_bv 64 A -> ew E 32 = Z_to_bv 64 b -> ew E 26 = Z_to_bv 64 p ->
  0 <= A -> 0 <= b < 256 -> 0 <= p < 256 -> A + 3 * b + p < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff n 0) OFF0) = Z_to_bv 64 (A + 3 * b + p).
Proof.
  intros E n A b p HA Hb Hp HA0 Hbr Hpr Hlt.
  rewrite denot_lit_U. f_equal. unfold OFF0.
  rewrite !U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E n A HA ltac:(lia)), (U_atom E 32 b Hb ltac:(lia)), (U_atom E 26 p Hp ltac:(lia)).
  rewrite U_SLit, (zcanon_id 1) by (unfold M64; lia).
  change (Z.land 1 63) with 1. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  rewrite (zcanon_id (b * 2)) by (unfold M64; lia).
  rewrite (zcanon_id (b * 2 + b)) by (unfold M64; lia).
  rewrite (zcanon_id (p + (b * 2 + b))) by (unfold M64; lia).
  rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* The shadow byte's address of x: (x >> 3) + SHADOW_OFF. *)
Lemma denot_shb : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 47 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SLit SB3)) = Z_to_bv 64 (SHADOW_OFF + x / 8).
Proof.
  intros E n x Hx Hr.
  rewrite denot_lit_U. f_equal.
  rewrite !U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n x Hx ltac:(lia)), !U_SLit.
  rewrite (zcanon_id 3) by (unfold M64; lia). change (Z.land 3 63) with 3.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (0 <= x / 8 <= x) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  rewrite (zcanon_id (x / 8)) by (unfold M64; lia).
  unfold SB3, SHADOW_OFF. rewrite (zcanon_id 2147450880) by (unfold M64; lia).
  rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma mod32_8 : forall F, F mod 32 = 0 -> F mod 8 = 0.
Proof.
  intros F H. apply Z.mod_divide in H; [|lia]. destruct H as [q ->].
  replace (q * 32) with ((4 * q) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma div8_split : forall F x, F mod 8 = 0 -> (F + x) / 8 = F / 8 + x / 8.
Proof.
  intros F x H. pose proof (Z.div_mod F 8 ltac:(lia)) as D. rewrite H, Z.add_0_r in D.
  rewrite D at 1. rewrite Z.mul_comm, Z.div_add_l by lia. reflexivity.
Qed.

(* ---- the regions of this part's symbolic states ---- *)
Lemma rok_RA3 : forall E (H : word -> bool) mem F b inn,
  ew E 18 = Z_to_bv 64 (F + 448) -> ew E 32 = Z_to_bv 64 b -> ew E 33 = Z_to_bv 64 inn ->
  aview SEGS H mem (F + 448) = Some b -> aview SEGS H mem (F + 449) = Some inn ->
  0 <= F -> F + 450 <= 2 ^ 47 ->
  YP09.region_ok SEGS E (mrestrict H mem) RA3.
Proof.
  intros E H mem F b inn E18 E32 E33 Hb Hi HF0 HF1.
  destruct (val_mem1_of_aview SEGS H mem (F + 448) b Hb) as [Vb Rb].
  destruct (val_mem1_of_aview SEGS H mem (F + 449) inn Hi) as [Vi Ri].
  unfold YP09.region_ok, RA3. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB E 18 (F + 448) E18) by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor; [|constructor]].
  - apply (chunk_ok_val SEGS E _ (F + 448) 0 1 (SOff 32 0) b); [rewrite sv_SOff0; exact E32 | zside | zside |].
    rewrite Z.add_0_r. exact Vb.
  - apply (chunk_ok_val SEGS E _ (F + 448) 1 1 (SOff 33 0) inn); [rewrite sv_SOff0; exact E33 | zside | zside |].
    replace (F + 448 + 1) with (F + 449) by lia. exact Vi.
Qed.

Lemma rok_RS3 : forall E (H : word -> bool) mem sp1 v8 v64 v136 v144,
  ew E 9 = Z_to_bv 64 sp1 -> ew E 34 = Z_to_bv 64 v8 -> ew E 35 = Z_to_bv 64 v64 ->
  ew E 36 = Z_to_bv 64 v136 -> ew E 37 = Z_to_bv 64 v144 ->
  rdword (aview SEGS H mem) (sp1 + 8) = Some v8 -> rdword (aview SEGS H mem) (sp1 + 64) = Some v64 ->
  rdword (aview SEGS H mem) (sp1 + 136) = Some v136 -> rdword (aview SEGS H mem) (sp1 + 144) = Some v144 ->
  rdword (aview SEGS H mem) (sp1 + 152) = Some SHADOW_OFF ->
  0 <= v8 < 2 ^ 64 -> 0 <= v64 < 2 ^ 64 -> 0 <= v136 < 2 ^ 64 -> 0 <= v144 < 2 ^ 64 ->
  0 <= sp1 -> sp1 + 160 <= 2 ^ 64 ->
  YP09.region_ok SEGS E (mrestrict H mem) RS3.
Proof.
  intros E H mem sp1 v8 v64 v136 v144 E9 E34 E35 E36 E37 S8 S64 S136 S144 S152 R8 R64 R136 R144 Hs0 Hs1.
  unfold YP09.region_ok, RS3. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB E 9 sp1 E9) by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val SEGS E _ sp1 8 8 (SOff 34 0) v8); [rewrite sv_SOff0; exact E34 | zside | zside |].
    exact (val_mem_of_rdword SEGS H mem _ _ S8).
  - apply (chunk_ok_val SEGS E _ sp1 64 8 (SOff 35 0) v64); [rewrite sv_SOff0; exact E35 | zside | zside |].
    exact (val_mem_of_rdword SEGS H mem _ _ S64).
  - apply (chunk_ok_val SEGS E _ sp1 136 8 (SOff 36 0) v136); [rewrite sv_SOff0; exact E36 | zside | zside |].
    exact (val_mem_of_rdword SEGS H mem _ _ S136).
  - apply (chunk_ok_val SEGS E _ sp1 144 8 (SOff 37 0) v144); [rewrite sv_SOff0; exact E37 | zside | zside |].
    exact (val_mem_of_rdword SEGS H mem _ _ S144).
  - apply (chunk_ok_val SEGS E _ sp1 152 8 (SLit SB3) SHADOW_OFF); [reflexivity | unfold SHADOW_OFF; zside | zside |].
    exact (val_mem_of_rdword SEGS H mem _ _ S152).
Qed.

Lemma rok_R1b : forall E (H : word -> bool) mem n v a x,
  ew E n = Z_to_bv 64 a -> ew E v = Z_to_bv 64 x -> aview SEGS H mem a = Some x -> 0 <= a < 2 ^ 63 ->
  YP09.region_ok SEGS E (mrestrict H mem) (R1b n v).
Proof.
  intros E H mem n v a x En Ev Hx Ha.
  destruct (val_mem1_of_aview SEGS H mem a x Hx) as [Vx Rx].
  unfold YP09.region_ok, R1b. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB E n a En) by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ a 0 1 (SOff v 0) x); [rewrite sv_SOff0; exact Ev | zside | zside |].
  rewrite Z.add_0_r. exact Vx.
Qed.

Lemma rok_R1z : forall E (H : word -> bool) mem n a,
  ew E n = Z_to_bv 64 a -> aview SEGS H mem a = Some 0 -> 0 <= a < 2 ^ 63 ->
  YP09.region_ok SEGS E (mrestrict H mem) (R1z n).
Proof.
  intros E H mem n a En Hx Ha.
  destruct (val_mem1_of_aview SEGS H mem a 0 Hx) as [Vx Rx].
  unfold YP09.region_ok, R1z. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB E n a En) by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ a 0 1 (SLit 0) 0); [reflexivity | zside | zside |].
  rewrite Z.add_0_r. exact Vx.
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
Lemma zext_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
  sv_denot E (SAlu ALU_AND (SOff n 0) (SLit 255)) = Z_to_bv 64 v.
Proof.
  intros E n v H Hv. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E n v H) by lia. rewrite U_SLit, (zcanon_id 255) by (unfold M64; lia).
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
Ltac rawreg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation GF := (fun GI => ge_from B MT (ge_post B MT) GI).

Definition g0_inv (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (t s : Z) (p : nat) : Prop :=
  ge_body cx fp GPS_ga0 W3 ms3 GSH_a /\ k <= 2 /\ acc <= GE_A2 MT - mo_free MT /\
  gsw_blk B cx fp ly3 S3 W3 ms3 t s /\ gsw_rows cx W3 ms3 t s /\
  (p < 3)%nat /\
  getr (ms_regs ms3) 26 = w64 (Z.of_nat p) /\
  getr (ms_regs ms3) 27 = w64 (s + 34 + 34 * Z.of_nat p) /\
  getr (ms_regs ms3) 21 = w64 3 /\ getr (ms_regs ms3) 18 = w64 (gF cx fp + GO_A) /\
  getr (ms_regs ms3) 22 = w64 (gSH cx fp) /\ getr (ms_regs ms3) 23 = w64 SHADOW_OFF.

(* The two program functions a turn calls, by their own contracts. *)
Hypothesis THD : treac_headamp_default_spec B.
Hypothesis TCG : tcheck_groupa_spec B.

(* What a turn leaves at 0x810ac, when check_groupa has returned: the journal grows, the
   blocks and the frames stay, the registers the loop keeps are kept, and so is every byte
   the cuts name. *)
Definition g0_mid (cx : ecx) (fp k : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (t s : Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 (Z_to_bv 64 (BASE + GPS_cga0)) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(GE_CID, fp)] ly2 S2 W2 mem2 md2 k /\
    YG01.frames S2 = YG01.frames S3 /\ ablocks B ly2 S2 = ablocks B ly3 S3 /\ (exists f, S2 = set_fs f S3) /\
    (forall r : bv 5, In r g0_kl -> getr regs2 r = getr (ms_regs ms3) r) /\
    vkeep (gsw_out cx fp t s) W3 (ms_mem ms3) W2 mem2.

Section d.
Hypothesis RT : GSW_RT B MT.
Let LAWS : AR_laws SEGS B := proj1 RT.

(* The symbolic state at 0x8103c, from the cut's facts. *)
Lemma g0_seat : forall cx fp k ly3 S3 W3 ms3 md3 t s (p : nat),
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  YG01.frames S3 = [(GE_CID, fp)] ->
  ge_body cx fp GPS_ga0 W3 ms3 GSH_a -> gsw_blk B cx fp ly3 S3 W3 ms3 t s -> gsw_rows cx W3 ms3 t s ->
  (p < 3)%nat -> getr (ms_regs ms3) 26 = w64 (Z.of_nat p) ->
  getr (ms_regs ms3) 18 = w64 (gF cx fp + GO_A) -> getr (ms_regs ms3) 23 = w64 SHADOW_OFF ->
  st_ok_pi SEGS VAL (Eg (ms_regs ms3) (g0_xs cx fp s (Z.of_nat p))) ss_g0
    (restrict (w_H W3) (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + GPS_ga0)) (ms_mem ms3) (seg_rom SEGS))).
Proof.
  intros cx fp k ly3 S3 W3 ms3 md3 t s p HB HJ HFR HBD HBLK HROWS Hp R26 R18 R23.
  pose proof HBD as (_ & _ & _ & _ & _ & _ & (G2 & G8 & G9 & G3 & G4) & _ & HSH & _ & HLEN & _).
  pose proof HBLK as (Hab3 & Hins & (Hint & Ht0 & HTl & HTb) & HWS & HST & HREL & HI1 & HSL & HS88 & HS120 & HS96 & HS64
    & H20 & Hcn & Ht & Hs & HAB).
  destruct HSL as ((M16 & M24 & M48 & M56 & M136 & M144 & M152 & M176) & L8 & L32 & L40 & L72 & L80 & L104 & L112 & L128).
  pose proof HROWS as (Hok & Hwant & HSW).
  rewrite Hok in HAB. destruct HAB as (A0 & A1). unfold gfb, GO_A in A0, A1.
  destruct (gsw_bounds B MT cx fp k ly3 S3 W3 (ms_mem ms3) md3 t s HB HJ HFR Hint Hins LAWS)
    as (Hal & Hsp0 & H47 & Hsp1 & Hsp32 & HF0 & HFc & HF32 & Ht0' & Htc & Hs0 & Hsc & HPB).
  pose proof (ok_bounds _ Hok) as (Bb0 & Bi1 & Bi40 & Bbi).
  pose proof (@alloc_ceiling_value rc) as HAC. unfold GE_STK in Hsp0.
  pose proof (sw_mbytes_ge (c_pl cx)) as Hsm.
  assert (Hfin : In (GE_CID, fp) (YG01.frames S3)) by (rewrite HFR; left; reflexivity).
  destruct (al_frames _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 GE_CID fp (proj1 HJ) Hfin) as (_ & Happ & _).
  pose proof HJ as (_ & Hly & _).
  assert (EF : frame_addr ly3 GE_CID fp = gF cx fp).
  { unfold gF, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  rewrite EF in Happ. change (fs_frame_bytes GE_CID) with 1024 in Happ.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
  pose proof (mod32_8 _ HF32) as HF8.
  set (b := sw_base (c_pl cx)) in *. set (inn := sw_in (c_pl cx)) in *.
  set (i := g0_i (c_pl cx) (Z.of_nat p)).
  assert (Hi : 0 <= i <= 143) by (unfold i, g0_i; fold b; lia).
  pose proof (Z.div_mod (GO_WAS + i) 8 ltac:(lia)) as DW. pose proof (Z.mod_pos_bound (GO_WAS + i) 8 ltac:(lia)) as MW.
  pose proof (Z.div_mod (GO_SET + i) 8 ltac:(lia)) as DS. pose proof (Z.mod_pos_bound (GO_SET + i) 8 ltac:(lia)) as MS.
  pose proof (Z.div_mod (gF cx fp) 8 ltac:(lia)) as DF.
  unfold GO_WAS, GO_SET in DW, MW, DS, MS.
  assert (KW : 4 <= (32 + i) / 8 <= 21) by lia.
  assert (KS : 30 <= (240 + i) / 8 <= 47) by lia.
  (* the bytes the regions read *)
  assert (Vws : aview SEGS (w_H W3) (ms_mem ms3) (gF cx fp + GO_WAS + i) = Some (tb (ws_end (c_pl cx)) i)).
  { unfold gfarr in HWS. destruct (garr8_nthZ SEGS _ _ _ i HWS ltac:(lia) ltac:(rewrite length_map, length_ws_end; lia)) as [Hv Hr].
    rewrite nth_map_bu in Hv, Hr. fold (tb (ws_end (c_pl cx)) i) in Hv, Hr.
    exact (aview_of_val_mem1 SEGS _ _ _ _ Hv Hr). }
  assert (Vst : aview SEGS (w_H W3) (ms_mem ms3) (gF cx fp + GO_SET + i) = Some (tb (st_end (c_pl cx)) i)).
  { unfold gfarr in HST. destruct (garr8_nthZ SEGS _ _ _ i HST ltac:(lia) ltac:(rewrite length_map, length_st_end; lia)) as [Hv Hr].
    rewrite nth_map_bu in Hv, Hr. fold (tb (st_end (c_pl cx)) i) in Hv, Hr.
    exact (aview_of_val_mem1 SEGS _ _ _ _ Hv Hr). }
  assert (Zsh : forall d, (4 <= d <= 21) \/ (30 <= d <= 47) ->
            aview SEGS (w_H W3) (ms_mem ms3) (SHADOW_OFF + gF cx fp / 8 + d) = Some 0).
  { intros d Hd. specialize (HSH (Z.to_nat d) ltac:(rewrite HLEN; unfold GE_NSH; lia)).
    rewrite Z2Nat.id in HSH by lia. rewrite GSH_a_zero in HSH by lia.
    unfold gSH, shadow_of_addr in HSH. exact HSH. }
  rewrite restrict_mkst_fx. unfold ss_g0. apply pa_entry_st_ok_full.
  - apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | cbn [sv_denot]; rewrite R23; reflexivity].
  - vm_compute. reflexivity.
  - set (E := Eg (ms_regs ms3) (g0_xs cx fp s (Z.of_nat p))).
    assert (E9 : ew E 9 = Z_to_bv 64 (c_sp1 cx)) by (unfold E; rewrite (Eg_reg _ _ 9 9%bv eq_refl); exact G9).
    assert (E18 : ew E 18 = Z_to_bv 64 (gF cx fp + 448)) by (unfold E; rewrite (Eg_reg _ _ 18 18%bv eq_refl); exact R18).
    unfold g0_regions. repeat apply Forall_cons; try apply Forall_nil.
    + apply (rok_RA3 E _ _ (gF cx fp) b inn E18 (Eg_x _ _ 0 ltac:(cbv; lia)) (Eg_x _ _ 1 ltac:(cbv; lia)) A0 A1); lia.
    + apply (rok_RS3 E _ _ (c_sp1 cx) (gF cx fp + GO_POLL) s (gF cx fp + GO_SET) (gF cx fp + GO_WAS) E9
        (Eg_x _ _ 2 ltac:(cbv; lia)) (Eg_x _ _ 3 ltac:(cbv; lia)) (Eg_x _ _ 4 ltac:(cbv; lia)) (Eg_x _ _ 5 ltac:(cbv; lia))
        L8 HS64 M136 M144 M152); unfold GO_POLL, GO_SET, GO_WAS; lia.
    + apply (rok_R1b E _ _ 38 39 (gF cx fp + GO_WAS + i) (tb (ws_end (c_pl cx)) i)
        (Eg_x _ _ 6 ltac:(cbv; lia)) (Eg_x _ _ 7 ltac:(cbv; lia)) Vws). unfold GO_WAS; lia.
    + apply (rok_R1z E _ _ 42 (SHADOW_OFF + gF cx fp / 8 + (GO_WAS + i) / 8) (Eg_x _ _ 10 ltac:(cbv; lia))).
      * apply Zsh. unfold GO_WAS. lia.
      * unfold SHADOW_OFF, GO_WAS. lia.
    + apply (rok_R1b E _ _ 40 41 (gF cx fp + GO_SET + i) (tb (st_end (c_pl cx)) i)
        (Eg_x _ _ 8 ltac:(cbv; lia)) (Eg_x _ _ 9 ltac:(cbv; lia)) Vst). unfold GO_SET; lia.
    + apply (rok_R1z E _ _ 43 (SHADOW_OFF + gF cx fp / 8 + (GO_SET + i) / 8) (Eg_x _ _ 11 ltac:(cbv; lia))).
      * apply Zsh. unfold GO_SET. lia.
      * unfold SHADOW_OFF, GO_SET. lia.
  - set (E := Eg (ms_regs ms3) (g0_xs cx fp s (Z.of_nat p))).
    assert (E9 : ew E 9 = Z_to_bv 64 (c_sp1 cx)) by (unfold E; rewrite (Eg_reg _ _ 9 9%bv eq_refl); exact G9).
    assert (E18 : ew E 18 = Z_to_bv 64 (gF cx fp + 448)) by (unfold E; rewrite (Eg_reg _ _ 18 18%bv eq_refl); exact R18).
    unfold g0_regions, RA3, RS3, R1b, R1z. cbn [YP09.pairwise_disjoint YP09.all_disjoint].
    unfold YP09.extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB E 9 _ E9) by lia. rewrite (VB E 18 _ E18) by lia.
    rewrite (VB E 38 (gF cx fp + GO_WAS + i) (Eg_x _ _ 6 ltac:(cbv; lia))) by (unfold GO_WAS; lia).
    rewrite (VB E 40 (gF cx fp + GO_SET + i) (Eg_x _ _ 8 ltac:(cbv; lia))) by (unfold GO_SET; lia).
    rewrite (VB E 42 (SHADOW_OFF + gF cx fp / 8 + (GO_WAS + i) / 8) (Eg_x _ _ 10 ltac:(cbv; lia))) by (unfold SHADOW_OFF, GO_WAS; lia).
    rewrite (VB E 43 (SHADOW_OFF + gF cx fp / 8 + (GO_SET + i) / 8) (Eg_x _ _ 11 ltac:(cbv; lia))) by (unfold SHADOW_OFF, GO_SET; lia).
    unfold SHADOW_OFF, GO_WAS, GO_SET.
    repeat split; lia.
  - set (E := Eg (ms_regs ms3) (g0_xs cx fp s (Z.of_nat p))).
    assert (E26 : ew E 26 = Z_to_bv 64 (Z.of_nat p)) by (unfold E; rewrite (Eg_reg _ _ 26 26%bv eq_refl); exact R26).
    pose proof (tb_range (ws_end (c_pl cx)) i) as Tw. pose proof (tb_range (st_end (c_pl cx)) i) as Ts.
    assert (E32 : ew E 32 = Z_to_bv 64 b) by exact (Eg_x _ _ 0 ltac:(cbv; lia)).
    assert (E33 : ew E 33 = Z_to_bv 64 inn) by exact (Eg_x _ _ 1 ltac:(cbv; lia)).
    assert (E36 : ew E 36 = Z_to_bv 64 (gF cx fp + GO_SET)) by exact (Eg_x _ _ 4 ltac:(cbv; lia)).
    assert (E37 : ew E 37 = Z_to_bv 64 (gF cx fp + GO_WAS)) by exact (Eg_x _ _ 5 ltac:(cbv; lia)).
    assert (E38 : ew E 38 = Z_to_bv 64 (gF cx fp + GO_WAS + i)) by exact (Eg_x _ _ 6 ltac:(cbv; lia)).
    assert (E39 : ew E 39 = Z_to_bv 64 (tb (ws_end (c_pl cx)) i)) by exact (Eg_x _ _ 7 ltac:(cbv; lia)).
    assert (E40 : ew E 40 = Z_to_bv 64 (gF cx fp + GO_SET + i)) by exact (Eg_x _ _ 8 ltac:(cbv; lia)).
    assert (E41 : ew E 41 = Z_to_bv 64 (tb (st_end (c_pl cx)) i)) by exact (Eg_x _ _ 9 ltac:(cbv; lia)).
    assert (E42 : ew E 42 = Z_to_bv 64 (SHADOW_OFF + gF cx fp / 8 + (GO_WAS + i) / 8)) by exact (Eg_x _ _ 10 ltac:(cbv; lia)).
    assert (E43 : ew E 43 = Z_to_bv 64 (SHADOW_OFF + gF cx fp / 8 + (GO_SET + i) / 8)) by exact (Eg_x _ _ 11 ltac:(cbv; lia)).
    split; [|split; [exact I|]].
    + cbn [f_atoms g0_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E26, E32, E33, E39, E41, !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat split; lia.
    + cbn [f_alias g0_alias alias_ok].
      split; [|split; [|split; [|split; [|exact I]]]].
      * rewrite sv_SOff0, E38.
        rewrite (denot_off0 E 37 (gF cx fp + GO_WAS) b (Z.of_nat p) E37 E32 E26) by (unfold GO_WAS; lia).
        f_equal. unfold i, g0_i. fold b. lia.
      * rewrite sv_SOff0, E42.
        rewrite (denot_shb E 38 (gF cx fp + GO_WAS + i) E38) by (unfold GO_WAS; lia).
        f_equal. rewrite <- Z.add_assoc, div8_split by exact HF8. lia.
      * rewrite sv_SOff0, E40.
        rewrite (denot_off0 E 36 (gF cx fp + GO_SET) b (Z.of_nat p) E36 E32 E26) by (unfold GO_SET; lia).
        f_equal. unfold i, g0_i. fold b. lia.
      * rewrite sv_SOff0, E43.
        rewrite (denot_shb E 40 (gF cx fp + GO_SET + i) E40) by (unfold GO_SET; lia).
        f_equal. rewrite <- Z.add_assoc, div8_split by exact HF8. lia.
Qed.

Let MTF : ameter_fs_laws MT := proj1 (proj2 (proj2 (proj2 RT))).
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Lemma g0_kl_ap : forall (r0 r1 : bvmap 5 word), aregs_preserved r0 r1 ->
  forall r : bv 5, In r g0_kl -> getr r1 r = getr r0 r.
Proof.
  intros r0 r1 H r Hr. apply (ap_list r0 r1 H). unfold g0_kl in Hr.
  repeat (destruct Hr as [<-|Hr]; [kl_in|]). destruct Hr.
Qed.

(* ---- the call of check_groupa at 0x810a8 ---- *)
(* From the cut at 0x8103c to the return of check_groupa, once the walk stands at the
   call with row 1 + p in a0, a.base in a1, p in a2, the table in a3 and the value the
   table gives in a4. *)
Lemma g0_cga_at : forall cx fp k acc ly3 S3 W3 ms3 t s (p : nat) (regsT : bvmap 5 word) memT mdT,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 memT mdT k ->
  YG01.frames S3 = [(GE_CID, fp)] ->
  g0_inv cx fp k acc ly3 S3 W3 ms3 t s p ->
  (forall x, memT x = ms_mem ms3 x) ->
  (forall r : bv 5, In r g0_kl -> getr regsT r = getr (ms_regs ms3) r) ->
  getr regsT 1 = Z_to_bv 64 (BASE + GPS_cga0) ->
  getr regsT 10 = getr (ms_regs ms3) 27 ->
  getr regsT 11 = Z_to_bv 64 (sw_base (c_pl cx)) ->
  getr regsT 12 = Z_to_bv 64 (Z.of_nat p) ->
  getr regsT 13 = getr (ms_regs ms3) 20 ->
  getr regsT 14 = Z_to_bv 64 (eff (T_end (c_pl cx)) t (sw_base (c_pl cx)) (Z.of_nat p)) ->
  SRr SEGS W3 (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA GS_check_groupa)) memT (seg_rom SEGS)) mdT)
    (g0_mid cx fp k ly3 S3 W3 ms3 t s).
Proof.
  intros cx fp k acc ly3 S3 W3 ms3 t s p regsT memT mdT HB HJ HFR HI HM KR R1 R10 R11 R12 R13 R14.
  destruct HI as (HBD & Hk & Hacc & HBLK & HROWS & Hp & R26 & R27 & R21 & R18 & R22 & R23).
  pose proof HBD as (_ & _ & _ & _ & _ & _ & (G2 & G8 & G9 & G3 & G4) & (S8 & S16) & _).
  pose proof HBLK as (Hab & Hins & (Hint & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & H20 & _).
  pose proof HROWS as (Hok & Hwant & HSW).
  destruct (gsw_bounds B MT cx fp k ly3 S3 W3 memT mdT t s HB HJ HFR Hint Hins LAWS)
    as (Hal & Hsp0 & H47 & Hsp1 & Hsp32 & HF0 & HFc & HF32 & Ht0' & Htc & Hs0 & Hsc & HPB).
  pose proof (ok_bounds _ Hok) as (Bb0 & Bi1 & Bi40 & Bbi).
  pose proof (sw_bytes_len cx t Hok Hwant) as Hswl.
  pose proof (length_sweep_ge (sw_base (c_pl cx)) (Z.to_nat (sw_in (c_pl cx))) (sw_vals (c_pl cx) t)) as Hsw170.
  fold (sw_bytes (c_pl cx) t) in Hsw170.
  assert (LG : forall a b c, length (GAz a b c) = 34%nat) by reflexivity.
  assert (VK0 : vkeep (gsw_out cx fp t s) W3 (ms_mem ms3) W3 memT) by (apply vkeep_mem; exact HM).
  assert (BLKT : gsw_blk B cx fp ly3 S3 W3 (mkst regsT (Z_to_bv 64 0) memT (seg_rom SEGS)) t s).
  { apply (gsw_blk_move B cx fp ly3 S3 W3 ms3 ly3 S3 W3 (mkst regsT (Z_to_bv 64 0) memT (seg_rom SEGS)) t s
      HBLK eq_refl VK0); [lia|].
    cbn [ms_regs mkst]. apply KR. kl_in. }
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
  assert (Q10 : getr regsT 10 = w64 (s + 34 + 34 * Z.of_nat p)) by (rewrite R10; exact R27).
  assert (Q13 : getr regsT 13 = w64 t) by (rewrite R13; exact H20).
  eapply SRr_mono.
  { exact (gsw_cga B MT LAWS TCG cx fp k ly3 S3 W3 regsT memT mdT GPS_cga0 t s (s + 34 + 34 * Z.of_nat p)
      (sw_base (c_pl cx)) (Z.of_nat p) HB HJ HFR BLKT Q2 Q3 Q4 Q8 R1 ltac:(unfold GPS_cga0; lia) eq_refl H8 H16
      Q10 R11 R12 Q13 R14 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HROW). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & Hfr2 & Hab2 & Hfs & HP & HK).
  exists ly2, S2, regs2, mem2, md2.
  split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hfr2|]. split; [exact Hab2|]. split; [exact Hfs|].
  split; [intros r Hr; rewrite (g0_kl_ap _ _ HP r Hr); exact (KR r Hr)|].
  exact (vkeep_trans _ _ _ _ _ _ _ VK0 HK).
Qed.

(* ---- one turn: 0x8103c -> the return of check_groupa at 0x810ac ---- *)
Lemma g0_turn : forall cx fp k acc ly3 S3 W3 ms3 md3 t s (p : nat),
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  YG01.frames S3 = [(GE_CID, fp)] ->
  g0_inv cx fp k acc ly3 S3 W3 ms3 t s p ->
  SRr SEGS W3 (mkCfg ms3 md3) (g0_mid cx fp k ly3 S3 W3 ms3 t s).
Proof.
  intros cx fp k acc ly3 S3 W3 ms3 md3 t s p HB HJ HFR HI.
  pose proof HI as (HBD & Hk & Hacc & HBLK & HROWS & Hp & R26 & R27 & R21 & R18 & R22 & R23).
  pose proof HBD as (Hpc & Hrv & Hsv & Hrom & Hfr & Hfc & (G2 & G8 & G9 & G3 & G4) & (S8 & S16) & _).
  pose proof HBLK as (Hab & Hins & (Hint & Ht0 & _) & _ & _ & HREL & _).
  pose proof HROWS as (Hok & Hwant & HSW).
  pose proof (ok_bounds _ Hok) as (Bb0 & Bi1 & Bi40 & Bbi).
  destruct (gsw_bounds B MT cx fp k ly3 S3 W3 (ms_mem ms3) md3 t s HB HJ HFR Hint Hins LAWS)
    as (Hal & Hsp0 & H47 & Hsp1 & Hsp32 & HF0 & HFc & HF32 & Ht0' & Htc & Hs0 & Hsc & HPB).
  pose proof (want_eff (c_pl cx) t (sw_base (c_pl cx)) p ltac:(lia) Ht0 Hp HREL) as HWE.
  fold (g0_i (c_pl cx) (Z.of_nat p)) in HWE.
  pose proof (tb_range (ws_end (c_pl cx)) (g0_i (c_pl cx) (Z.of_nat p))) as Tw.
  pose proof (tb_range (st_end (c_pl cx)) (g0_i (c_pl cx) (Z.of_nat p))) as Ts.
  pose proof (g0_seat cx fp k ly3 S3 W3 ms3 md3 t s p HB HJ HFR HBD HBLK HROWS Hp R26 R18 R23) as HS.
  remember (g0_mid cx fp k ly3 S3 W3 ms3 t s) as Q eqn:HQ.
  rewrite (ms_shape ms3 (BASE + GPS_ga0) Hpc Hrv Hsv Hrom Hfr Hfc).
  remember (Eg (ms_regs ms3) (g0_xs cx fp s (Z.of_nat p))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg (ms_regs ms3) (map (Z_to_bv 64) (g0_xs cx fp s (Z.of_nat p)))) E)
    by (subst E; apply env_agree_Eimg).
  assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r)
    by (intros n r Hn; subst E; apply Eg_reg; exact Hn).
  assert (E32 : ew E 32 = Z_to_bv 64 (sw_base (c_pl cx))) by (subst E; exact (Eg_x _ _ 0 ltac:(cbv; lia))).
  assert (E39 : ew E 39 = Z_to_bv 64 (tb (ws_end (c_pl cx)) (g0_i (c_pl cx) (Z.of_nat p))))
    by (subst E; exact (Eg_x _ _ 7 ltac:(cbv; lia))).
  assert (E41 : ew E 41 = Z_to_bv 64 (tb (st_end (c_pl cx)) (g0_i (c_pl cx) (Z.of_nat p))))
    by (subst E; exact (Eg_x _ _ 9 ltac:(cbv; lia))).
  assert (E26 : ew E 26 = Z_to_bv 64 (Z.of_nat p)) by (rewrite (ER 26%nat 26%bv eq_refl); exact R26).
  clear HE.
  assert (SHOK : sh_ok SEGS Bx3 [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  (* run 1: 0x8103c -> `beqz a2` at 0x81068; the shadow check of was_set[i] at 0x81060
     reads the region of its shadow byte, which is 0 *)
  paj_run_tok RUN HS HJ SHOK Bsp3; [g0_awr|].
  g0_mem HM1.
  lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msA end.
  psrr_branch_tok RUN BR HS SHOK Bsp3.
  - (* was_set[i] = 0: a4 = reac_headamp_default(p) *)
    rewrite branch_eq_U, (U_atom E 39 _ E39), U_lit in Hc by lia.
    apply Z.eqb_eq in Hc.
    (* run 2: 0x8106c -> the call at 0x81090 *)
    paj_run_tok RUN HS HJ SHOK Bsp3; [g0_awr|].
    g0_mem HM2.
    lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msH end.
    pose proof (regs_kept_of_st_ok SEGS _ _ _ (ms_regs ms3) _ g0_kl0 HS HAE ltac:(vm_compute; reflexivity)) as KF.
    cbn [ms_regs restrict] in KF.
    prreg HS (23%bv : bv 5) H23. prreg HS (24%bv : bv 5) H24.
    prreg HS (1%bv : bv 5) Ra. prreg HS (10%bv : bv 5) Ra0.
    assert (KRH : forall r : bv 5, In r g0_kl -> getr (ms_regs msH) r = getr (ms_regs ms3) r)
      by (kl_cases KF H23 R23).
    pmkst HS.
    eapply SRr_bind.
    { apply (gsw_hdflt B MT LAWS THD cx fp k ly3 S3 W3 (ms_regs msH) (ms_mem msH) _ GPS_hdef (Z.of_nat p) HB HJ).
      - rewrite KRH by kl_in. exact G2.
      - rewrite KRH by kl_in. exact G3.
      - rewrite KRH by kl_in. exact G4.
      - rewrite KRH by kl_in. exact G8.
      - rewrite Ra. reflexivity.
      - unfold GPS_hdef. lia.
      - reflexivity.
      - rewrite HM2, HM1. exact S8.
      - rewrite HM2, HM1. pose proof (S16 0 ltac:(lia)) as Hj0.
        replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in Hj0 by lia.
        cbn [Z.ltb Z.compare] in Hj0. exact Hj0.
      - rewrite Ra0, E26. reflexivity.
      - lia. }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H10 & HM3).
    clear HS SHOK KF Ra Ra0.
    (* run 3: 0x81094 -> the call of check_groupa at 0x810a8 *)
    pose proof (plain_entry W3 regs2 mem2 GPS_hdef) as HS2.
    remember (Eimg (Ereg regs2 [])) as E2 eqn:HE2.
    assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
    assert (HAE2 : env_agree 32 (Ereg regs2 []) E2) by (subst E2; apply env_agree_Eimg).
    assert (ER2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs2 r)
      by (intros n r Hn; subst E2; apply ew_Eimg_Ereg_nat; exact Hn).
    clear HE2.
    assert (SHOK2 : sh_ok SEGS Bx3 [] E2 (mrestrict (w_H W3) mem2)) by constructor.
    paj_run_tok RUN HS2 HJ2 SHOK2 Bsp3; [g0_awr|].
    g0_mem HM4.
    lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msC end.
    pose proof (regs_kept_of_st_ok SEGS _ _ _ regs2 _ g0_kl HS2 HAE2 ltac:(vm_compute; reflexivity)) as KF2.
    cbn [ms_regs restrict] in KF2.
    assert (KRC : forall r : bv 5, In r g0_kl -> getr (ms_regs msC) r = getr (ms_regs ms3) r).
    { intros r Hr. rewrite (KF2 r Hr), (g0_kl_ap _ _ HP2 r Hr). exact (KRH r Hr). }
    prreg HS2 (1%bv : bv 5) Ra. prreg HS2 (10%bv : bv 5) Ra0. prreg HS2 (11%bv : bv 5) Ra1.
    rawreg HS2 (12%bv : bv 5) Ra2. prreg HS2 (13%bv : bv 5) Ra3. prreg HS2 (14%bv : bv 5) Ra4.
    pmkst HS2. subst Q.
    apply (g0_cga_at cx fp k acc ly3 S3 W3 ms3 t s p (ms_regs msC) (ms_mem msC) _ HB HJ2 HFR HI).
    + intros x. rewrite HM4, HM3, HM2, HM1. reflexivity.
    + exact KRC.
    + rewrite Ra. reflexivity.
    + rewrite Ra0, (ER2 27%nat 27%bv eq_refl), (g0_kl_ap _ _ HP2 27%bv ltac:(kl_in)). apply KRH. kl_in.
    + rewrite Ra1, (ER2 24%nat 24%bv eq_refl). apg HP2 (24%bv : bv 5) 24. rewrite H24. exact E32.
    + rewrite Ra2. apply zext_atom; [|lia].
      rewrite (ER2 26%nat 26%bv eq_refl), (g0_kl_ap _ _ HP2 26%bv ltac:(kl_in)), (KRH 26%bv ltac:(kl_in)).
      exact R26.
    + rewrite Ra3, (ER2 20%nat 20%bv eq_refl), (g0_kl_ap _ _ HP2 20%bv ltac:(kl_in)). apply KRH. kl_in.
    + rewrite Ra4, (ER2 10%nat 10%bv eq_refl), H10, HWE, Hc. reflexivity.
  - (* was_set[i] <> 0: a4 = set_to[i]; the shadow check of set_to[i] at 0x81080 reads
       the region of its shadow byte, which is 0 *)
    rewrite branch_eq_U, (U_atom E 39 _ E39), U_lit in Hc by lia.
    apply Z.eqb_neq in Hc.
    (* run 2: 0x8106c -> the call of check_groupa at 0x810a8 *)
    paj_run_tok RUN HS HJ SHOK Bsp3; [g0_awr|].
    g0_mem HM2.
    lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msC end.
    pose proof (regs_kept_of_st_ok SEGS _ _ _ (ms_regs ms3) _ g0_kl0 HS HAE ltac:(vm_compute; reflexivity)) as KF.
    cbn [ms_regs restrict] in KF.
    prreg HS (23%bv : bv 5) H23.
    assert (KRC : forall r : bv 5, In r g0_kl -> getr (ms_regs msC) r = getr (ms_regs ms3) r)
      by (kl_cases KF H23 R23).
    prreg HS (1%bv : bv 5) Ra. prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1.
    rawreg HS (12%bv : bv 5) Ra2. prreg HS (13%bv : bv 5) Ra3. prreg HS (14%bv : bv 5) Ra4.
    pmkst HS. subst Q.
    apply (g0_cga_at cx fp k acc ly3 S3 W3 ms3 t s p (ms_regs msC) (ms_mem msC) _ HB HJ HFR HI).
    + intros x. rewrite HM2, HM1. reflexivity.
    + exact KRC.
    + rewrite Ra. reflexivity.
    + rewrite Ra0. apply ER. reflexivity.
    + rewrite Ra1. exact E32.
    + rewrite Ra2. apply zext_atom; [exact E26 | lia].
    + rewrite Ra3. apply ER. reflexivity.
    + rewrite Ra4, E41, HWE, (proj2 (Z.eqb_neq _ _) Hc). reflexivity.
Qed.

(* ---- the symbolic state at 0x810ac, after check_groupa ---- *)
Lemma g0x_seat : forall cx fp k ly3 S3 W3 ms3 md3 t s (p : nat) (W2 : world SEGS) (regs2 : bvmap 5 word) mem2,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  YG01.frames S3 = [(GE_CID, fp)] ->
  gsw_blk B cx fp ly3 S3 W3 ms3 t s -> gsw_rows cx W3 ms3 t s ->
  getr regs2 9 = w64 (c_sp1 cx) -> getr regs2 18 = w64 (gF cx fp + GO_A) ->
  vkeep (gsw_out cx fp t s) W3 (ms_mem ms3) W2 mem2 ->
  st_ok_pi SEGS VAL (Eg regs2 (g0_xs cx fp s (Z.of_nat p))) ss_g0x
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + GPS_cga0)) mem2 (seg_rom SEGS))).
Proof.
  intros cx fp k ly3 S3 W3 ms3 md3 t s p W2 regs2 mem2 HB HJ HFR HBLK HROWS R9 R18 VK.
  pose proof HBLK as (Hab3 & Hins & (Hint & Ht0 & HTl & HTb) & HWS & HST & HREL & HI1 & HSL & HS88 & HS120 & HS96 & HS64
    & H20 & Hcn & Ht & Hs & HAB).
  destruct HSL as ((M16 & M24 & M48 & M56 & M136 & M144 & M152 & M176) & L8 & L32 & L40 & L72 & L80 & L104 & L112 & L128).
  pose proof HROWS as (Hok & Hwant & HSW).
  rewrite Hok in HAB. destruct HAB as (A0 & A1). unfold gfb, GO_A in A0, A1.
  destruct (gsw_bounds B MT cx fp k ly3 S3 W3 (ms_mem ms3) md3 t s HB HJ HFR Hint Hins LAWS)
    as (Hal & Hsp0 & H47 & Hsp1 & Hsp32 & HF0 & HFc & HF32 & Ht0' & Htc & Hs0 & Hsc & HPB).
  pose proof (ok_bounds _ Hok) as (Bb0 & Bi1 & Bi40 & Bbi).
  pose proof (@alloc_ceiling_value rc) as HAC. unfold GE_STK in Hsp0.
  pose proof (sw_mbytes_ge (c_pl cx)) as Hsm.
  (* the two bytes of `a` and the five spill slots, through the call *)
  assert (A0' : aview SEGS (w_H W2) mem2 (gF cx fp + 448) = Some (sw_base (c_pl cx))).
  { rewrite (VK (gF cx fp + 448)); [exact A0 | left; right; right; left; lia]. }
  assert (A1' : aview SEGS (w_H W2) mem2 (gF cx fp + 449) = Some (sw_in (c_pl cx))).
  { rewrite (VK (gF cx fp + 449)); [exact A1 | left; right; right; left; lia]. }
  assert (KS : forall off v, 8 <= off <= 152 -> rdword (aview SEGS (w_H W3) (ms_mem ms3)) (c_sp1 cx + off) = Some v ->
             rdword (aview SEGS (w_H W2) mem2) (c_sp1 cx + off) = Some v).
  { intros off v Hoff Hr. eapply rdword_vkeep; [exact VK | | exact Hr]. intros kk Hkk. left; left. lia. }
  rewrite restrict_mkst_fx. unfold ss_g0x. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - set (E := Eg regs2 (g0_xs cx fp s (Z.of_nat p))).
    assert (E9 : ew E 9 = Z_to_bv 64 (c_sp1 cx)) by (unfold E; rewrite (Eg_reg _ _ 9 9%bv eq_refl); exact R9).
    assert (E18 : ew E 18 = Z_to_bv 64 (gF cx fp + 448)) by (unfold E; rewrite (Eg_reg _ _ 18 18%bv eq_refl); exact R18).
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (rok_RA3 E _ _ (gF cx fp) (sw_base (c_pl cx)) (sw_in (c_pl cx)) E18
        (Eg_x _ _ 0 ltac:(cbv; lia)) (Eg_x _ _ 1 ltac:(cbv; lia)) A0' A1'); lia.
    + apply (rok_RS3 E _ _ (c_sp1 cx) (gF cx fp + GO_POLL) s (gF cx fp + GO_SET) (gF cx fp + GO_WAS) E9
        (Eg_x _ _ 2 ltac:(cbv; lia)) (Eg_x _ _ 3 ltac:(cbv; lia)) (Eg_x _ _ 4 ltac:(cbv; lia)) (Eg_x _ _ 5 ltac:(cbv; lia))
        (KS 8 _ ltac:(lia) L8) (KS 64 _ ltac:(lia) HS64) (KS 136 _ ltac:(lia) M136) (KS 144 _ ltac:(lia) M144)
        (KS 152 _ ltac:(lia) M152)); unfold GO_POLL, GO_SET, GO_WAS; lia.
  - set (E := Eg regs2 (g0_xs cx fp s (Z.of_nat p))).
    assert (E9 : ew E 9 = Z_to_bv 64 (c_sp1 cx)) by (unfold E; rewrite (Eg_reg _ _ 9 9%bv eq_refl); exact R9).
    assert (E18 : ew E 18 = Z_to_bv 64 (gF cx fp + 448)) by (unfold E; rewrite (Eg_reg _ _ 18 18%bv eq_refl); exact R18).
    unfold RA3, RS3. cbn [YP09.pairwise_disjoint YP09.all_disjoint].
    unfold YP09.extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB E 9 _ E9) by lia. rewrite (VB E 18 _ E18) by lia.
    repeat split; lia.
  - set (E := Eg regs2 (g0_xs cx fp s (Z.of_nat p))).
    assert (E33 : ew E 33 = Z_to_bv 64 (sw_in (c_pl cx))) by exact (Eg_x _ _ 1 ltac:(cbv; lia)).
    split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E33, !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; lia.
Qed.

Section e.
Hypothesis NEXT1 : GF (GIS_ga1 B MT).
Hypothesis NEXT2 : GF (GIS_gbhd B MT).

(* ---- after check_groupa: 0x810ac -> 0x8103c, 0x81104 or 0x811f8 ---- *)
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
  g0_mid cx fp k ly3 S3 W3 ms3 t s W2 c2 ->
  SRr SEGS W2 c2 (ge_post B MT cx).
Proof.
  intros cx fp k acc ly3 S3 W3 ms3 md3 t s p W2 c2 HB HJ HFR Hmo HI IH HM.
  destruct HM as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & Hfr2 & Hab2 & (f & ES2) & KR & VK).
  pose proof HI as (HBD & Hk & Hacc & HBLK & HROWS & Hp & R26 & R27 & R21 & R18 & R22 & R23).
  pose proof HBD as (Hpc & Hrv & Hsv & Hrom & Hfr & Hfc & (G2 & G8 & G9 & G3 & G4) & _).
  pose proof HBLK as (Hab & Hins & (Hint & Ht0 & _) & _).
  pose proof HROWS as (Hok & Hwant & HSW).
  pose proof (ok_bounds _ Hok) as (Bb0 & Bi1 & Bi40 & Bbi).
  destruct (gsw_bounds B MT cx fp k ly3 S3 W3 (ms_mem ms3) md3 t s HB HJ HFR Hint Hins LAWS)
    as (Hal & Hsp0 & H47 & Hsp1 & Hsp32 & HF0 & HFc & HF32 & Ht0' & Htc & Hs0 & Hsc & HPB).
  pose proof (@alloc_ceiling_value rc) as HAC. unfold GE_STK in Hsp0.
  pose proof (sw_mbytes_ge (c_pl cx)) as Hsm.
  assert (HFR2 : YG01.frames S2 = [(GE_CID, fp)]) by (rewrite Hfr2; exact HFR).
  assert (Hmo2 : mo_le MT (c_S cx) S2 acc) by (rewrite ES2; apply (mo_le_set_fs_r MT MTF); exact Hmo).
  assert (R9' : getr regs2 9 = w64 (c_sp1 cx)) by (rewrite KR by kl_in; exact G9).
  assert (R18' : getr regs2 18 = w64 (gF cx fp + GO_A)) by (rewrite KR by kl_in; exact R18).
  pose proof (g0x_seat cx fp k ly3 S3 W3 ms3 md3 t s p W2 regs2 mem2 HB HJ HFR HBLK HROWS R9' R18' VK) as HS.
  remember (Eg regs2 (g0_xs cx fp s (Z.of_nat p))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs2 (map (Z_to_bv 64) (g0_xs cx fp s (Z.of_nat p)))) E)
    by (subst E; apply env_agree_Eimg).
  assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
    by (intros n r Hn; subst E; apply Eg_reg; exact Hn).
  assert (E33 : ew E 33 = Z_to_bv 64 (sw_in (c_pl cx))) by (subst E; exact (Eg_x _ _ 1 ltac:(cbv; lia))).
  assert (E34 : ew E 34 = Z_to_bv 64 (gF cx fp + GO_POLL)) by (subst E; exact (Eg_x _ _ 2 ltac:(cbv; lia))).
  assert (E35 : ew E 35 = Z_to_bv 64 s) by (subst E; exact (Eg_x _ _ 3 ltac:(cbv; lia))).
  clear HE.
  assert (EK : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> In r g0_kl -> ew E n = getr (ms_regs ms3) r)
    by (intros n r Hn Hr; rewrite (ER n r Hn); exact (KR r Hr)).
  assert (E26 : ew E 26 = Z_to_bv 64 (Z.of_nat p)) by (rewrite (EK 26%nat 26%bv eq_refl) by kl_in; exact R26).
  assert (E27 : ew E 27 = Z_to_bv 64 (s + 34 + 34 * Z.of_nat p))
    by (rewrite (EK 27%nat 27%bv eq_refl) by kl_in; exact R27).
  assert (E21 : ew E 21 = Z_to_bv 64 3) by (rewrite (EK 21%nat 21%bv eq_refl) by kl_in; exact R21).
  assert (E22 : ew E 22 = Z_to_bv 64 (gSH cx fp)) by (rewrite (EK 22%nat 22%bv eq_refl) by kl_in; exact R22).
  assert (SHOK : sh_ok SEGS Bx3 [] E (mrestrict (w_H W2) mem2)) by constructor.
  (* run 1: 0x810ac -> `bne s10,s5` at 0x810b4 *)
  paj_run_tok RUN HS HJ2 SHOK Bsp3; [g0_awr|].
  g0_mem HM1.
  lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msB end.
  psrr_branch_tok RUN BR HS SHOK Bsp3.
  - (* p + 1 <> 3: back to the head 0x8103c with p + 1 *)
    rewrite branch_ne_U, (U_atom_off E 26 (Z.of_nat p) 1 E26), (U_atom E 21 3 E21) in Hc by lia.
    apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ2 SHOK Bsp3 GPS_ga0; [g0_awr|].
    g0_mem HM2.
    lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msF end.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 _ g0_kl1 HS HAE ltac:(vm_compute; reflexivity)) as KF.
    cbn [ms_regs restrict] in KF.
    assert (KRF : forall r : bv 5, In r g0_kl1 -> getr (ms_regs msF) r = getr (ms_regs ms3) r).
    { intros r Hr. rewrite (KF r Hr). apply KR. unfold g0_kl1 in Hr.
      repeat (destruct Hr as [<-|Hr]; [kl_in|]). destruct Hr. }
    prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
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
    split; [eapply gsw_blk_move; [exact HBLK | exact Hab2 | exact VKF | lia | cbn [ms_regs mkst]; apply KRF; kl_in]|].
    split; [eapply gsw_rows_move; [exact HROWS | exact VKF]|].
    split; [lia|].
    cbn [ms_regs mkst].
    split; [rewrite Q26, E26, unsigned_lit_small by lia; apply zeq64; lia|].
    split; [rewrite Q27, E27, unsigned_lit_small by lia; apply zeq64; lia|].
    split; [rewrite KRF by kl_in; exact R21|].
    split; [rewrite KRF by kl_in; exact R18|].
    split; [rewrite KRF by kl_in; exact R22|].
    rewrite KRF by kl_in. exact R23.
  - (* p + 1 = 3: the loop is done; `bltu a0,a1` at 0x810ec tests a.in < 2 *)
    clear Hc.
    paj_run_tok RUN HS HJ2 SHOK Bsp3; [g0_awr|].
    g0_mem HM2.
    lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msX end.
    psrr_branch_tok RUN BR HS SHOK Bsp3.
    + (* a.in < 2: on to group B, 0x811f8 with i = 0 *)
      rewrite branch_ltu_U, (U_atom E 33 _ E33), U_lit in Hc by lia.
      apply Z.ltb_lt in Hc.
      paj_run_to_tok RUNTO HS HJ2 SHOK Bsp3 GPS_gbhd; [g0_awr|].
      g0_mem HM3.
      lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msG end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 _ [2; 3; 4; 8; 9; 20; 22]%bv HS HAE
        ltac:(vm_compute; reflexivity)) as KF.
      cbn [ms_regs restrict] in KF.
      assert (KRG : forall r : bv 5, In r [2; 3; 4; 8; 9; 20; 22]%bv -> getr (ms_regs msG) r = getr (ms_regs ms3) r).
      { intros r Hr. rewrite (KF r Hr). apply KR.
        repeat (destruct Hr as [<-|Hr]; [kl_in|]). destruct Hr. }
      prreg HS (18%bv : bv 5) Q18. prreg HS (27%bv : bv 5) Q27. prreg HS (26%bv : bv 5) Q26.
      prreg HS (21%bv : bv 5) Q21. prreg HS (19%bv : bv 5) Q19. prreg HS (24%bv : bv 5) Q24.
      prreg HS (25%bv : bv 5) Q25. prreg HS (23%bv : bv 5) Q23.
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
      split; [eapply gsw_blk_move; [exact HBLK | exact Hab2 | exact VKG | lia | cbn [ms_regs mkst]; apply KRG; kl_in]|].
      split; [eapply gsw_rows_move; [exact HROWS | exact VKG]|].
      split; [lia|].
      cbn [ms_regs mkst].
      split; [rewrite Q18; reflexivity|].
      split; [rewrite Q27, E35, unsigned_lit_small by lia; apply zeq64; lia|].
      split; [rewrite Q26, (img_env_atomP E _ HEI) by (unfold A_TEXT, A_LIM; lia); apply zeq64;
              change (A_OBJ 6) with 247%nat; lia|].
      split; [rewrite Q21; reflexivity|].
      split; [rewrite Q19, E34; reflexivity|].
      split; [rewrite Q24; reflexivity|].
      split; [rewrite Q25; reflexivity|].
      split; [rewrite Q23; apply zeq64m; reflexivity|].
      rewrite KRG by kl_in. exact R22.
    + (* a.in >= 2: on to group A for the channels 1 .. w-1, 0x81104 with c = 1 *)
      rewrite branch_ltu_U, (U_atom E 33 _ E33), U_lit in Hc by lia.
      apply Z.ltb_ge in Hc.
      paj_run_to_tok RUNTO HS HJ2 SHOK Bsp3 GPS_ga1; [g0_awr|].
      g0_mem HM3.
      lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msG end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 _ [2; 3; 4; 8; 9; 18; 20; 22]%bv HS HAE
        ltac:(vm_compute; reflexivity)) as KF.
      cbn [ms_regs restrict] in KF.
      assert (KRG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 22]%bv -> getr (ms_regs msG) r = getr (ms_regs ms3) r).
      { intros r Hr. rewrite (KF r Hr). apply KR.
        repeat (destruct Hr as [<-|Hr]; [kl_in|]). destruct Hr. }
      prreg HS (21%bv : bv 5) Q21. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
      prreg HS (23%bv : bv 5) Q23. prreg HS (19%bv : bv 5) Q19.
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
      split; [eapply gsw_blk_move; [exact HBLK | exact Hab2 | exact VKG | lia | cbn [ms_regs mkst]; apply KRG; kl_in]|].
      split; [eapply gsw_rows_move; [exact HROWS | exact VKG]|].
      split; [lia|]. split; [lia|].
      cbn [ms_regs mkst].
      split; [rewrite Q21; reflexivity|].
      split; [rewrite Q24; reflexivity|].
      split; [rewrite Q25, E35, unsigned_lit_small by lia; apply zeq64; lia|].
      split; [rewrite KRG by kl_in; exact R18|].
      split; [rewrite Q23; reflexivity|].
      rewrite Q19, (ER 22%nat 22%bv eq_refl), KR by kl_in. exact R22.
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
  - exfalso. destruct HI as (_ & _ & _ & _ & _ & Hp & _). lia.
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

(* 0x8103c -> 0x81104 or 0x811f8: the first group-A loop, from the contracts of
   reac_headamp_default (HeadampDefault.v) and check_groupa (CheckGroupa.v). *)
Lemma gsw_seg_ga0 : SEG_ga0 B MT.
Proof. intros RT NEXT1 NEXT2. exact (g0_seg RT NEXT1 NEXT2). Qed.

End c.

End b.
End a.
