(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySweepS3b), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8v.v. *)
(* Segment 3, part b, of the sweep phase: 0x81104 -> 0x811f8 — the second group-A
   loop (fuzz_grant.c:328-332) and the block that sets the group-B loop up.

   For every channel c = 1 .. a.in - 1 and every parameter p = 0, 1, 2 the harness
   reads was_set[3 * (a.base + c) + p] in its own frame, takes set_to[...] or
   reac_headamp_default(p) as the value it wants, and calls check_groupa on sweep
   row 11 + 3 * (c - 1) + p. Both frame reads are checked against the shadow byte
   of the entry, which is 0 in GSH_a (the two calls of __asan_memset of the
   prologue marked both arrays usable), so neither branch to the memory-checking
   runtime's report (0x811a8 -> 0x81afc, 0x811b4 -> 0x81b0c) is taken.

   The walk is a nested induction: the outer one on the channels left
   (a.in - c), the inner one on the parameters left (3 - p), after cgif's
   tcbl_loop (proofs/cgif/cgif_file_fuzzer/lib/A/AC8c.v:47) and GrantEntrySweepS2.v.
   The two calls are GrantEntrySweepS3c.v's `gsw_hdflt` and GrantEntrySweepS3d.v's
   `gsw_cga`. *)
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
GrantFrame YC1g YC1h YC1i YC88 YC85 GrantEntrySweepS3c GrantEntrySweepS3d HeadampDefault CheckGroupa.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel GrantModel GrantSweepModel BuildSweepModel SweepRowCheck GrantSlotPlan.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require SlotNeeds_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ---- the listing offsets of this segment ---- *)
Definition GPS_g1in : Z := 0xa5c.   (* 0x8110c, the head of the parameter loop *)
Definition GPS_g1hd : Z := 0xac4.   (* 0x81174, after reac_headamp_default     *)
Definition GPS_g1cg : Z := 0xae0.   (* 0x81190, after check_groupa             *)

(* ---- the model facts of one turn ---- *)
Lemma g1_ok_bounds : forall pl, ok pl = true ->
  0 <= sw_base pl /\ 1 <= sw_in pl /\ sw_in pl <= 40 /\ sw_base pl + sw_in pl <= 48.
Proof.
  intros pl H. unfold ok, fits in H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1, H2, H3, H4. unfold sw_base, sw_in. lia.
Qed.

Lemma g1_nth_map_bu : forall (l : list byte) i,
  nth i (map (fun b : byte => bv_unsigned b) l) 0 = bv_unsigned (nth i l (Z_to_bv 8 0)).
Proof. induction l as [|x l IH]; intros [|i]; cbn [map nth]; try reflexivity. apply IH. Qed.

Lemma g1_nth_concat34 : forall (L : list (list byte)) k j, Forall (fun r => length r = 34%nat) L ->
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

(* Row 11 + 3 * (c - 1) + p of the sweep is Pau's group-A row for the channel
   a.base + c and the value the table gives (SweepRowCheck.v nth_row_A,
   BuildSweepModel.v nth_sweep_vals). *)
Lemma g1_sweep_row : forall T t base w (c p : nat) j, (1 <= c < w)%nat -> (p < 3)%nat -> (j < 34)%nat ->
  0 <= base -> base + Z.of_nat w <= 48 ->
  nth (34 * (11 + 3 * (c - 1) + p) + j)
      (map (fun b : byte => bv_unsigned b) (SWEEP base w (sweep_vals T t base w))) 0 =
  nth j (GAz (base + Z.of_nat c) (Z.of_nat p) (eff T t (base + Z.of_nat c) (Z.of_nat p))) 0.
Proof.
  intros T t base w c p j Hc Hp Hj Hb Hw.
  rewrite g1_nth_map_bu, SWEEP_rows.
  rewrite g1_nth_concat34; [| apply Forall_rowok_len, sweep_rows_ok | | exact Hj].
  2:{ pose proof (length_sweep_rows base w (sweep_vals T t base w) ltac:(lia)). lia. }
  rewrite nth_row_A by first [lia | exact Hp]. unfold ga_row, vz.
  rewrite (nth_sweep_vals T t base w c p (Z_to_bv 8 0)) by lia.
  rewrite bv8_small by (apply eff_range).
  rewrite (Z.mod_small (base + Z.of_nat c)) by lia.
  pose proof (eff_range T t (base + Z.of_nat c) (Z.of_nat p)) as Hv.
  rewrite <- g1_nth_map_bu. unfold GA. rewrite map_unsigned_bl; [reflexivity|].
  apply GA_bytes_range; lia.
Qed.

(* The value the harness wants for (ch, p) is the table's effective value
   (GrantSlotPlan.v Hrel, HeadampModel.v eff_cell). *)
Lemma g1_want_eff : forall pl t ch (p : nat), 0 < t -> (p < 3)%nat -> 0 <= ch < 48 ->
  Hrel (T_end pl) (ws_end pl) (st_end pl) ->
  eff (T_end pl) t ch (Z.of_nat p) =
  if tb (ws_end pl) (3 * ch + Z.of_nat p) =? 0 then dflt (Z.of_nat p)
  else tb (st_end pl) (3 * ch + Z.of_nat p).
Proof.
  intros pl t ch p Ht Hp Hch HR. rewrite eff_cell by lia.
  destruct (HR ch (Z.of_nat p) ltac:(lia) ltac:(lia)) as [H1 H2]. rewrite H1, H2. reflexivity.
Qed.

(* The shadow bytes of was_set and of set_to are 0 in GSH_a. *)
Lemma g1_GSH_a_zero : forall k, (4 <= k < 22)%nat \/ (30 <= k < 48)%nat -> nth k GSH_a 0 = 0.
Proof.
  intros k Hk. assert (Hk' : (k < 48)%nat) by lia.
  do 48 (destruct k as [|k]; [first [reflexivity | lia] |]). lia.
Qed.

Lemma g1_GSH_a_len : length GSH_a = 104%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma g1_tb_range : forall l i, 0 <= tb l i < 256.
Proof. intros l i. unfold tb. apply u8_range. Qed.

Lemma g1_afact : forall (E : env) n lo hi v,
  ew E n = w64 v -> 0 <= lo -> lo <= v <= hi -> hi < 2 ^ 64 -> afact_ok E n (mkAF lo hi 0).
Proof.
  intros E n lo hi v H Hlo Hv Hhi. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite H. unfold w64. rewrite unsigned_lit_small by lia.
  rewrite Z.pow_0_r, Z.mod_1_r. split; [lia|]. split; [reflexivity | lia].
Qed.

(* ---- the symbolic state of the three runs of one turn ---- *)
(* Atoms: 32 a.base, 33 a.in, 34 the sweep block s, 35 gF + GO_SET, 36 the channel
   a.base + c, 37 gF + GO_WAS, 38 the address of was_set[i], 39 its value,
   40 the address of set_to[i], 41 its value. Atom 18 is s2, which holds the
   address of `a`, and atom 9 is s1, the realigned machine stack pointer. *)
Definition g1_IDX : sv := SAlu ALU_ADD (SOff 26 0) (SMd M_MUL (SOff 36 0) (SLit 3)).
Definition g1_alias : list (sv * sv) :=
  [ (SAlu ALU_ADD (SOff 24 0) (SOff 32 0), SOff 36 0);
    (SAlu ALU_ADD (SOff 32 0) (SOff 21 0), SOff 36 0);
    (SAlu ALU_AND (SOff 36 0) (SLit 255), SOff 36 0);
    (SAlu ALU_AND (SOff 26 0) (SLit 255), SOff 26 0);
    (SAlu ALU_ADD (SOff 37 0) g1_IDX, SOff 38 0);
    (SAlu ALU_ADD (SOff 35 0) g1_IDX, SOff 40 0) ].
Definition g1_atoms : list (nat * afact) :=
  [ (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0); (36%nat, mkAF 0 255 0);
    (38%nat, mkAF 4096 0x7fffff800000 0); (39%nat, mkAF 0 255 0);
    (40%nat, mkAF 4096 0x7fffff800000 0); (41%nat, mkAF 0 255 0) ].
Definition g1_SH : list shent := [mkSHE 38 0 1; mkSHE 40 0 1].
(* a.base and a.in, the two bytes of the allocation the loop reads. *)
Definition g1_RA : YP09.region :=
  YP09.mkRegion (Some 18%nat) 0 2 0 0
    [YP09.mkChunk 0 (CVal 1 (SOff 32 0)); YP09.mkChunk 1 (CVal 1 (SOff 33 0))].
(* The spill slots the loop reads back: 64 the sweep block, 136 set_to, 144 was_set,
   152 the shadow offset. *)
Definition g1_RS : YP09.region :=
  YP09.mkRegion (Some 9%nat) 8 160 0 0
    [YP09.mkChunk 64 (CVal 8 (SOff 34 0)); YP09.mkChunk 136 (CVal 8 (SOff 35 0));
     YP09.mkChunk 144 (CVal 8 (SOff 37 0)); YP09.mkChunk 152 (CVal 8 (SLit SB3))].
(* The slots the block at 0x811cc reads: 8 the poll buffer, 64 the sweep block. *)
Definition g1_RS2 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 8 72 0 0
    [YP09.mkChunk 8 (CVal 8 (SOff 34 0)); YP09.mkChunk 64 (CVal 8 (SOff 35 0))].
Definition g1_R1 (n v : nat) : YP09.region :=
  YP09.mkRegion (Some n) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff v 0))].
Definition g1_regions : YP09.smem := [g1_RA; g1_RS; g1_R1 38 39; g1_R1 40 41].
Definition ss_g1 : sstate := mkSS GPS_g1in sr_atoms g1_regions None (mkFacts g1_atoms [] g1_alias).
(* After reac_headamp_default: the loop reads nothing until check_groupa. Atom 32
   is the channel here, and atom 22 the byte a.base the loop read before the call. *)
Definition ss_g1hd : sstate :=
  mkSS GPS_g1hd sr_atoms [] None
    (mkFacts [(32%nat, mkAF 0 255 0)] []
      [(SAlu ALU_ADD (SOff 22 0) (SOff 21 0), SOff 32 0);
       (SAlu ALU_AND (SOff 32 0) (SLit 255), SOff 32 0);
       (SAlu ALU_AND (SOff 26 0) (SLit 255), SOff 26 0)]).
(* After check_groupa: the loop test, then a.in and the slots of the group-B loop.
   Atom 34 is gF + GO_POLL and atom 35 the sweep block here. *)
Definition ss_g1cg : sstate :=
  mkSS GPS_g1cg sr_atoms [g1_RA; g1_RS2] None
    (mkFacts [(21%nat, mkAF 1 40 0); (33%nat, mkAF 0 255 0)] [] []).

(* the index of the cell of (ch, p) in was_set and in set_to *)
Definition g1_i (ch : Z) (p : nat) : Z := 3 * ch + Z.of_nat p.
(* the row of the sweep this turn checks *)
Definition g1_row (s : Z) (c p : nat) : Z := s + 34 * (11 + 3 * (Z.of_nat c - 1) + Z.of_nat p).

(* After a run: every region of this walk is read-only, so the memory is the one the
   run started from. *)
Ltac g1_mem HF HM :=
  lazymatch type of HF with
  | frame_of ?E ?rs ?m ?m' =>
      pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as HM
  end.

(* A callee-saved register at a call is the one at the head of the turn: through the
   run (`HS`, environment fact `XR`), or through a call before it (`HS2`, `XR2`, `HP2`). *)
Ltac g1_rk HS XR :=
  lazymatch goal with |- getr _ ?r = _ =>
    let R := fresh "R" in prreg HS r R; rewrite R; clear R; apply XR; reflexivity end.
Ltac g1_rk2 HS2 XR2 HP2 HS XR :=
  lazymatch goal with |- getr _ ?r = _ =>
    let R := fresh "R" in prreg HS2 r R; rewrite R; clear R;
    lazymatch goal with |- ew _ ?n = _ => rewrite (XR2 n r eq_refl) end;
    let z := eval vm_compute in (bv_unsigned r) in
    rewrite (ap_get _ _ r z eq_refl ltac:(unfold acallee_saved; lia) HP2);
    let R' := fresh "R" in prreg HS r R'; rewrite R'; clear R';
    apply XR; reflexivity end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
Context {RO : ro_below_ofl (@pa_segs _ grant_listing PI) (@pa_relro_lo _ grant_listing PI) (@pa_relro_hi _ grant_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Lemma g1_sv0 : forall (E : env) n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof.
  intros E n v H Hv. cbn [sv_denot]. rewrite H. unfold w64.
  rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
Qed.

(* A one-byte region whose base is an atom and whose byte is another atom. *)
Lemma g1_region1 : forall (E : env) m n v a b,
  ew E n = w64 a -> ew E v = w64 b -> 0 <= a -> a + 1 <= 2 ^ 64 -> 0 <= b < 256 ->
  val_mem SEGS m a 1 b ->
  YP09.region_ok SEGS E m (g1_R1 n v).
Proof.
  intros E m n v a b Hn Hv Ha0 Ha1 Hb Hm. unfold g1_R1, YP09.region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
  rewrite Hn. unfold w64. rewrite unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E m a 0 1%N (SOff v 0) b).
  - apply (g1_sv0 E v b Hv). lia.
  - cbn [Z.of_N]. change (8 * 1) with 8. lia.
  - cbn [Z.of_N]. lia.
  - cbn [N.to_nat]. rewrite Z.add_0_r. exact Hm.
Qed.

Lemma g1_regionA : forall (E : env) m a b0 b1,
  ew E 18 = w64 a -> ew E 32 = w64 b0 -> ew E 33 = w64 b1 ->
  0 <= a -> a + 2 <= 2 ^ 64 -> 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  val_mem SEGS m a 1 b0 -> val_mem SEGS m (a + 1) 1 b1 ->
  YP09.region_ok SEGS E m g1_RA.
Proof.
  intros E m a b0 b1 H18 H32 H33 Ha0 Ha1 Hb0 Hb1 Hm0 Hm1. unfold g1_RA, YP09.region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
  rewrite H18. unfold w64. rewrite unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (chunk_ok_val SEGS E m a 0 1%N (SOff 32 0) b0).
    + apply (g1_sv0 E 32 b0 H32). lia.
    + cbn [Z.of_N]. change (8 * 1) with 8. lia.
    + cbn [Z.of_N]. lia.
    + cbn [N.to_nat]. rewrite Z.add_0_r. exact Hm0.
  - apply (chunk_ok_val SEGS E m a 1 1%N (SOff 33 0) b1).
    + apply (g1_sv0 E 33 b1 H33). lia.
    + cbn [Z.of_N]. change (8 * 1) with 8. lia.
    + cbn [Z.of_N]. lia.
    + cbn [N.to_nat]. exact Hm1.
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis THD : treac_headamp_default_spec B.
Hypothesis TCG : tcheck_groupa_spec B.

Lemma g1_regionS : forall (E : env) (W : world SEGS) (ms : machine_state) (cx : ecx) s se sw,
  ew E 9 = w64 (c_sp1 cx) -> ew E 34 = w64 s -> ew E 35 = w64 se -> ew E 37 = w64 sw ->
  0 <= c_sp1 cx -> c_sp1 cx + 160 <= 2 ^ 64 ->
  0 <= s < 2 ^ 64 -> 0 <= se < 2 ^ 64 -> 0 <= sw < 2 ^ 64 ->
  gslot cx W ms 64 s -> gslot cx W ms 136 se -> gslot cx W ms 144 sw ->
  gslot cx W ms 152 SHADOW_OFF ->
  YP09.region_ok SEGS E (mrestrict (w_H W) (ms_mem ms)) g1_RS.
Proof.
  intros E W ms cx s se sw H9 H34 H35 H37 Hs0 Hs1 Rs Rse Rsw G64 G136 G144 G152.
  unfold g1_RS, YP09.region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
  rewrite H9. unfold w64. rewrite unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  assert (CH : forall off e v, sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
    gslot cx W ms off v ->
    YP09.chunk_ok SEGS E (mrestrict (w_H W) (ms_mem ms)) (c_sp1 cx) (YP09.mkChunk off (CVal 8 e))).
  { intros off e v He Hv Hg.
    apply (chunk_ok_val SEGS E (mrestrict (w_H W) (ms_mem ms)) (c_sp1 cx) off 8%N e v).
    - exact He.
    - cbn [Z.of_N]. change (8 * 8) with 64. exact Hv.
    - cbn [Z.of_N]. lia.
    - cbn [N.to_nat]. apply (val_mem_of_rdword SEGS (w_H W) (ms_mem ms)). exact Hg. }
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
  - apply (CH 64 (SOff 34 0) s); [apply (g1_sv0 E 34 s H34); lia | lia | exact G64].
  - apply (CH 136 (SOff 35 0) se); [apply (g1_sv0 E 35 se H35); lia | lia | exact G136].
  - apply (CH 144 (SOff 37 0) sw); [apply (g1_sv0 E 37 sw H37); lia | lia | exact G144].
  - apply (CH 152 (SLit SB3) SHADOW_OFF); [reflexivity | unfold SHADOW_OFF; lia | exact G152].
Qed.

Lemma g1_regionS2 : forall (E : env) (W : world SEGS) (ms : machine_state) (cx : ecx) po s,
  ew E 9 = w64 (c_sp1 cx) -> ew E 34 = w64 po -> ew E 35 = w64 s ->
  0 <= c_sp1 cx -> c_sp1 cx + 72 <= 2 ^ 64 -> 0 <= po < 2 ^ 64 -> 0 <= s < 2 ^ 64 ->
  gslot cx W ms 8 po -> gslot cx W ms 64 s ->
  YP09.region_ok SEGS E (mrestrict (w_H W) (ms_mem ms)) g1_RS2.
Proof.
  intros E W ms cx po s H9 H34 H35 Hs0 Hs1 Rpo Rs G8 G64.
  unfold g1_RS2, YP09.region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
  rewrite H9. unfold w64. rewrite unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  assert (CH : forall off e v, sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
    gslot cx W ms off v ->
    YP09.chunk_ok SEGS E (mrestrict (w_H W) (ms_mem ms)) (c_sp1 cx) (YP09.mkChunk off (CVal 8 e))).
  { intros off e v He Hv Hg.
    apply (chunk_ok_val SEGS E (mrestrict (w_H W) (ms_mem ms)) (c_sp1 cx) off 8%N e v).
    - exact He.
    - cbn [Z.of_N]. change (8 * 8) with 64. exact Hv.
    - cbn [Z.of_N]. lia.
    - cbn [N.to_nat]. apply (val_mem_of_rdword SEGS (w_H W) (ms_mem ms)). exact Hg. }
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (CH 8 (SOff 34 0) po); [apply (g1_sv0 E 34 po H34); lia | lia | exact G8].
  - apply (CH 64 (SOff 35 0) s); [apply (g1_sv0 E 35 s H35); lia | lia | exact G64].
Qed.

(* The frame is in the part of memory the program may use, so none of its bytes is a
   shadow byte (the `app_apart` side of a shadow entry). *)
Lemma g1_frame_app : AR_laws SEGS B -> forall cx fp k ly3 S3 W3 memc mdc,
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 memc mdc k ->
  YG01.frames S3 = [(GE_CID, fp)] ->
  in_app (gF cx fp) 1024.
Proof.
  intros LAWS cx fp k ly3 S3 W3 memc mdc HJ Hfr.
  pose proof (proj1 HJ) as HAR. pose proof HJ as (_ & Hly & _).
  assert (Hin : In (GE_CID, fp) (YG01.frames S3)) by (rewrite Hfr; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS ly3 S3 W3 memc mdc GE_CID fp HAR Hin) as (_ & _ & HFia).
  assert (EF : gF cx fp = frame_addr ly3 GE_CID fp).
  { unfold gF, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  rewrite EF. change 1024 with (fs_frame_bytes GE_CID). exact HFia.
Qed.

(* The shadow byte of a cell of was_set or of set_to is 0, so the cell is addressable. *)
Lemma g1_cell_addressable : forall cx fp (W3 : world SEGS) (ms3 : machine_state) off i,
  gshadow cx fp W3 ms3 GSH_a ->
  gF cx fp mod 32 = 0 -> 4096 <= gF cx fp -> gF cx fp + 1024 <= alloc_ceiling ->
  (off = GO_WAS \/ off = GO_SET) -> 0 <= i < 144 ->
  range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF (gF cx fp + off + i) 1.
Proof.
  intros cx fp W3 ms3 off i HSH H32 HF0 HFc Hoff Hi x Hx.
  pose proof (eq_refl : GO_WAS = 32) as HW32.
  pose proof (eq_refl : GO_SET = 240) as HS240.
  assert (Hxe : x = gF cx fp + off + i) by lia. subst x.
  pose proof (Z.div_mod (gF cx fp) 32 ltac:(lia)) as D32.
  pose proof (Z.div_pos (gF cx fp) 32 ltac:(lia) ltac:(lia)) as Dpos.
  set (q := gF cx fp / 32) in *.
  assert (HF : gF cx fp = 32 * q) by lia.
  set (j := (off + i) / 8).
  assert (Hoi : 32 <= off + i < 384) by (destruct Hoff as [-> | ->]; lia).
  assert (Hj : 4 <= j < 48).
  { subst j. split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]. }
  assert (HjZ : 4 <= j < 22 \/ 30 <= j < 48).
  { destruct Hoff as [-> | ->]; [left | right]; subst j;
    (split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]). }
  assert (Hjr : (4 <= Z.to_nat j < 22)%nat \/ (30 <= Z.to_nat j < 48)%nat)
    by (destruct HjZ as [HR | HR]; [left | right]; lia).
  assert (Hsh : aview SEGS (w_H W3) (ms_mem ms3) (gSH cx fp + j) = Some 0).
  { replace (gSH cx fp + j) with (gSH cx fp + Z.of_nat (Z.to_nat j)) by lia.
    rewrite (HSH (Z.to_nat j) ltac:(rewrite g1_GSH_a_len; lia)).
    f_equal. apply g1_GSH_a_zero. exact Hjr. }
  exists 0. split; [| left; reflexivity].
  unfold shadow_of_addr, gSH, shadow_of_addr in *.
  replace (SHADOW_OFF + (gF cx fp + off + i) / 8) with (SHADOW_OFF + gF cx fp / 8 + j); [exact Hsh|].
  subst j. rewrite HF.
  replace (32 * q + off + i) with (off + i + 4 * q * 8) by lia.
  rewrite Z.div_add by lia.
  replace (32 * q) with (4 * q * 8) by lia.
  rewrite Z.div_mul by lia.
  lia.
Qed.

(* ---- the invariant of one turn, at the three pcs it passes ---- *)
Definition g1_at (pc : Z) (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (t s : Z) (c p : nat) : Prop :=
  ge_body cx fp pc W3 ms3 GSH_a /\ k <= 2 /\ acc <= GE_A2 MT - mo_free MT /\
  gsw_blk B cx fp ly3 S3 W3 ms3 t s /\ gsw_rows cx W3 ms3 t s /\
  (1 <= c)%nat /\ Z.of_nat c < sw_in (c_pl cx) /\ (p < 3)%nat /\
  getr (ms_regs ms3) 21 = w64 (Z.of_nat c) /\ getr (ms_regs ms3) 24 = w64 (Z.of_nat c) /\
  getr (ms_regs ms3) 25 = w64 (s + 374 + 102 * (Z.of_nat c - 1)) /\
  getr (ms_regs ms3) 18 = w64 (gF cx fp + GO_A) /\ getr (ms_regs ms3) 23 = w64 3 /\
  getr (ms_regs ms3) 19 = w64 (gSH cx fp) /\
  getr (ms_regs ms3) 26 = w64 (Z.of_nat p) /\
  getr (ms_regs ms3) 27 = w64 (g1_row s c p).

(* What the walk hands to the next cut inside the turn. *)
Definition g1_K (POST : ecx -> world SEGS -> config -> Prop) (pc : Z) (cx : ecx) (fp k acc t s : Z)
  (c p : nat) : Prop :=
  forall ly4 S4 W4 (ms4 : machine_state) md4,
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly4 S4 W4 (ms_mem ms4) md4 k ->
  YG01.frames S4 = [(GE_CID, fp)] ->
  mo_le MT (c_S cx) S4 acc ->
  g1_at pc cx fp k acc ly4 S4 W4 ms4 t s c p ->
  SRr SEGS W4 (mkCfg ms4 md4) (POST cx).

(* ---- the three alias facts the engine needs, at the value level ---- *)
Lemma g1_alias_add : forall (E : env) n m r a b,
  ew E n = w64 a -> ew E m = w64 b -> ew E r = w64 (a + b) ->
  0 <= a -> 0 <= b -> a + b < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff n 0) (SOff m 0)) = sv_denot E (SOff r 0).
Proof.
  intros E n m r a b Hn Hm Hr Ha Hb Hab. apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E n a) by first [exact Hn | lia].
  rewrite (U_atom E m b) by first [exact Hm | lia].
  rewrite (U_atom E r (a + b)) by first [exact Hr | lia].
  apply zcanon_id. unfold M64. lia.
Qed.

Lemma g1_alias_and : forall (E : env) n a, ew E n = w64 a -> 0 <= a < 256 ->
  sv_denot E (SAlu ALU_AND (SOff n 0) (SLit 255)) = sv_denot E (SOff n 0).
Proof.
  intros E n a H Ha. apply U_inj. rewrite U_and_lit by lia.
  rewrite (U_atom E n a) by first [exact H | lia].
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma g1_alias_idx : forall (E : env) n r a ch (p : nat),
  ew E n = w64 a -> ew E 36 = w64 ch -> ew E 26 = w64 (Z.of_nat p) ->
  ew E r = w64 (a + (Z.of_nat p + ch * 3)) ->
  0 <= a -> 0 <= ch < 256 -> (p < 3)%nat -> a + (Z.of_nat p + ch * 3) < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff n 0) g1_IDX) = sv_denot E (SOff r 0).
Proof.
  intros E n r a ch p Hn H36 H26 Hr Ha Hch Hp Hsum. apply U_inj.
  rewrite U_SAlu. cbn [zalu_raw]. unfold g1_IDX. rewrite U_SAlu. cbn [zalu_raw].
  rewrite U_SMd. cbn [zmd_raw].
  rewrite (U_atom E 36 ch) by first [exact H36 | lia].
  rewrite (U_atom E 26 (Z.of_nat p)) by first [exact H26 | lia].
  rewrite (U_lit E 3) by lia.
  rewrite (U_atom E n a) by first [exact Hn | lia].
  rewrite (U_atom E r (a + (Z.of_nat p + ch * 3))) by first [exact Hr | lia].
  rewrite (zcanon_id (ch * 3)) by (unfold M64; lia).
  rewrite (zcanon_id (Z.of_nat p + ch * 3)) by (unfold M64; lia).
  apply zcanon_id. unfold M64. lia.
Qed.

(* The extra atoms of the state at the head of the parameter loop. *)
Definition g1_ex (cx : ecx) (fp s ch iw : Z) : list word :=
  [w64 (sw_base (c_pl cx)); w64 (sw_in (c_pl cx)); w64 s; w64 (gF cx fp + GO_SET);
   w64 ch; w64 (gF cx fp + GO_WAS); w64 (gF cx fp + GO_WAS + iw); w64 (tb (ws_end (c_pl cx)) iw);
   w64 (gF cx fp + GO_SET + iw); w64 (tb (st_end (c_pl cx)) iw)].

Lemma g1_sweep_len : forall base w vals, (1 <= w)%nat ->
  Z.of_nat (length (SWEEP base w vals)) = 34 * (8 + 3 * Z.of_nat w).
Proof.
  intros base w vals Hw. rewrite SWEEP_rows.
  assert (HL : forall L : list (list byte), Forall (fun r => length r = 34%nat) L ->
    length (concat L) = (34 * length L)%nat).
  { induction L as [|r L IH]; intros HF; [reflexivity|]. inversion HF; subst. cbn [concat].
    rewrite length_app, IH by assumption. cbn [length]. lia. }
  rewrite HL by (apply Forall_rowok_len, sweep_rows_ok).
  rewrite Nat2Z.inj_mul, length_sweep_rows by lia. reflexivity.
Qed.

(* The two words of the machine frame a callee's call chain needs: ra and s0. *)
Lemma g1_saved : forall cx (W3 : world SEGS) (ms : machine_state), gsaved cx W3 ms ->
  rdword (aview SEGS (w_H W3) (ms_mem ms)) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) /\
  rdword (aview SEGS (w_H W3) (ms_mem ms)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)).
Proof.
  intros cx W3 ms (H8 & HJ). split; [exact H8|].
  pose proof (HJ 0 ltac:(lia)) as Hj0.
  replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in Hj0 by lia.
  cbn [Z.ltb Z.compare] in Hj0. exact Hj0.
Qed.

Lemma g1_GAz_len : forall ch p v, length (GAz ch p v) = 34%nat.
Proof. reflexivity. Qed.

Section d.
Hypothesis RT : GSW_RT B MT.
Let LAWS : AR_laws SEGS B := proj1 RT.
Let MFS : ameter_fs_laws MT := proj1 (proj2 (proj2 (proj2 RT))).
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* The call of check_groupa at 0x8118c, from the registers and memory the walk
   reached, and the landing at 0x81190 (GrantEntrySweepS3d.v gsw_cga). `ms0` is the
   state at the head of the parameter loop; the walk to the call wrote no memory
   and kept every callee-saved register. *)
Lemma g1_call : forall POST cx fp k acc ly3 S3 W3 (ms0 : machine_state) (regsT : bvmap 5 word) memT mdT
  t s c p,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 memT mdT k ->
  YG01.frames S3 = [(GE_CID, fp)] ->
  mo_le MT (c_S cx) S3 acc ->
  g1_at GPS_g1in cx fp k acc ly3 S3 W3 ms0 t s c p ->
  (forall x, memT x = ms_mem ms0 x) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27]%bv ->
     getr regsT r = getr (ms_regs ms0) r) ->
  getr regsT 1 = Z_to_bv 64 (BASE + GPS_g1cg) ->
  getr regsT 10 = w64 (g1_row s c p) ->
  getr regsT 11 = w64 (sw_base (c_pl cx) + Z.of_nat c) ->
  getr regsT 12 = w64 (Z.of_nat p) ->
  getr regsT 13 = w64 t ->
  getr regsT 14 = w64 (eff (T_end (c_pl cx)) t (sw_base (c_pl cx) + Z.of_nat c) (Z.of_nat p)) ->
  g1_K POST GPS_g1cg cx fp k acc t s c p ->
  SRr SEGS W3 (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA GS_check_groupa)) memT (seg_rom SEGS)) mdT) (POST cx).
Proof.
  intros POST cx fp k acc ly3 S3 W3 ms0 regsT memT mdT t s c p HB HJ Hfrm Hmo HG HM KR
    Rra R10 R11 R12 R13 R14 K.
  destruct HG as (HBD & Hk & Hacc & HBLK & HROWS & Hc1 & Hc2 & Hp3 & R21 & R24 & R25 & R18 & R23
    & R19 & R26 & R27).
  pose proof HBD as (_ & _ & _ & _ & _ & _ & (G2 & G8 & G9 & G3 & G4) & HSAV & _).
  pose proof HBLK as (Hab & Hins & HTAB & _ & _ & HREL & _ & _ & _ & _ & _ & _ & R20 & _ & Htpos & _).
  pose proof HTAB as (Hint & _).
  pose proof HROWS as (Hok & Hwant & HSW).
  destruct (gsw_bounds B MT cx fp k ly3 S3 W3 memT mdT t s HB HJ Hfrm Hint Hins LAWS)
    as (Hal & Hsp0 & H47 & Hsp1 & Hsp32 & HF0 & HFc & HF32 & Ht4096 & Htc & Hs4096 & Hsc & HPB).
  pose proof (g1_ok_bounds (c_pl cx) Hok) as (Hb0 & Hin1 & Hin40 & Hbw).
  pose proof (sw_bytes_len cx t Hok Hwant) as Hswl.
  assert (VK0 : vkeep (gsw_out cx fp t s) W3 (ms_mem ms0) W3 memT) by (apply vkeep_mem; exact HM).
  assert (K2 : getr regsT 2 = getr (ms_regs ms0) 2) by (apply KR; in_tac).
  assert (K3 : getr regsT 3 = getr (ms_regs ms0) 3) by (apply KR; in_tac).
  assert (K4 : getr regsT 4 = getr (ms_regs ms0) 4) by (apply KR; in_tac).
  assert (K8 : getr regsT 8 = getr (ms_regs ms0) 8) by (apply KR; in_tac).
  assert (K20 : getr regsT 20 = getr (ms_regs ms0) 20) by (apply KR; in_tac).
  assert (HBLKT : gsw_blk B cx fp ly3 S3 W3 (mkst regsT (Z_to_bv 64 0) memT (seg_rom SEGS)) t s).
  { eapply gsw_blk_move; [exact HBLK | reflexivity | exact VK0 | lia | exact K20]. }
  destruct (g1_saved cx W3 ms0 HSAV) as [H8 H16].
  assert (Hsweep : Z.of_nat (length (sw_bytes (c_pl cx) t)) = 34 * (8 + 3 * sw_in (c_pl cx))).
  { unfold sw_bytes. rewrite g1_sweep_len by lia. rewrite Z2Nat.id by lia. reflexivity. }
  assert (HROW : garr8 SEGS (mrestrict (w_H W3) memT) (g1_row s c p)
    (GAz (sw_base (c_pl cx) + Z.of_nat c) (Z.of_nat p)
         (eff (T_end (c_pl cx)) t (sw_base (c_pl cx) + Z.of_nat c) (Z.of_nat p)))).
  { replace (g1_row s c p) with (s + Z.of_nat (34 * (11 + 3 * (c - 1) + p))) by (unfold g1_row; lia).
    apply (garr8_slice _ s (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)) _
      (34 * (11 + 3 * (c - 1) + p))).
    - eapply garr8_vkeep; [exact VK0 | | exact HSW].
      intros a Ha. right; right. rewrite length_map in Ha. lia.
    - rewrite length_map, g1_GAz_len. lia.
    - intros j Hj. rewrite g1_GAz_len in Hj. unfold sw_bytes, sw_vals.
      apply g1_sweep_row; lia. }
  eapply SRr_bind.
  { apply (gsw_cga B MT LAWS TCG cx fp k ly3 S3 W3 regsT memT mdT GPS_g1cg t s (g1_row s c p)
      (sw_base (c_pl cx) + Z.of_nat c) (Z.of_nat p) HB HJ Hfrm HBLKT).
    - rewrite K2. exact G2.
    - rewrite K3. exact G3.
    - rewrite K4. exact G4.
    - rewrite K8. exact G8.
    - exact Rra.
    - unfold GPS_g1cg. lia.
    - reflexivity.
    - eapply rdword_vkeep; [exact VK0 | | exact H8]. intros kk Hkk. left; left. lia.
    - eapply rdword_vkeep; [exact VK0 | | exact H16]. intros kk Hkk. left; left. lia.
    - exact R10.
    - exact R11.
    - exact R12.
    - exact R13.
    - exact R14.
    - lia.
    - lia.
    - unfold g1_row. lia.
    - unfold sw_bytes in Hswl. unfold g1_row.
      rewrite g1_sweep_len in Hswl by lia. rewrite Z2Nat.id in Hswl by lia. lia.
    - exact HROW. }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & Hfr2 & Hab2 & (f & Hfs) & HP2 & HK2).
  assert (VK : vkeep (gsw_out cx fp t s) W3 (ms_mem ms0) W2 mem2) by (eapply vkeep_trans; [exact VK0 | exact HK2]).
  assert (KP : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27]%bv ->
    getr regs2 r = getr (ms_regs ms0) r).
  { intros r Hr. rewrite <- (KR r Hr).
    destruct Hr as [<-|Hr]; [apg HP2 (2%bv : bv 5) 2; reflexivity|].
    destruct Hr as [<-|Hr]; [apg HP2 (3%bv : bv 5) 3; reflexivity|].
    destruct Hr as [<-|Hr]; [apg HP2 (4%bv : bv 5) 4; reflexivity|].
    destruct Hr as [<-|Hr]; [apg HP2 (8%bv : bv 5) 8; reflexivity|].
    destruct Hr as [<-|Hr]; [apg HP2 (9%bv : bv 5) 9; reflexivity|].
    destruct Hr as [<-|Hr]; [apg HP2 (18%bv : bv 5) 18; reflexivity|].
    destruct Hr as [<-|Hr]; [apg HP2 (19%bv : bv 5) 19; reflexivity|].
    destruct Hr as [<-|Hr]; [apg HP2 (20%bv : bv 5) 20; reflexivity|].
    destruct Hr as [<-|Hr]; [apg HP2 (21%bv : bv 5) 21; reflexivity|].
    destruct Hr as [<-|Hr]; [apg HP2 (23%bv : bv 5) 23; reflexivity|].
    destruct Hr as [<-|Hr]; [apg HP2 (24%bv : bv 5) 24; reflexivity|].
    destruct Hr as [<-|Hr]; [apg HP2 (25%bv : bv 5) 25; reflexivity|].
    destruct Hr as [<-|Hr]; [apg HP2 (26%bv : bv 5) 26; reflexivity|].
    destruct Hr as [<-|[]]. apg HP2 (27%bv : bv 5) 27. reflexivity. }
  apply (K ly2 S2 W2 (mkst regs2 (Z_to_bv 64 (BASE + GPS_g1cg)) mem2 (seg_rom SEGS)) md2).
  - exact HJ2.
  - rewrite Hfr2. exact Hfrm.
  - rewrite Hfs. apply (mo_le_set_fs_r MT MFS). exact Hmo.
  - unfold g1_at. cbn [ms_regs mkst].
    split.
    { apply (ge_body_move cx fp GPS_g1in GPS_g1cg W3 W2 ms0 regs2 mem2 GSH_a HBD).
      - eapply vkeep_sub; [| exact VK]. intros a Ha. left. exact Ha.
      - lia.
      - apply KP; in_tac.
      - apply KP; in_tac.
      - apply KP; in_tac.
      - apply KP; in_tac.
      - apply KP; in_tac. }
    split; [exact Hk|]. split; [exact Hacc|].
    split.
    { eapply gsw_blk_move; [exact HBLK | exact Hab2 | exact VK | lia |]. cbn [ms_regs mkst]. apply KP; in_tac. }
    split; [eapply (gsw_rows_move cx fp); [exact HROWS | exact VK]|].
    split; [exact Hc1|]. split; [exact Hc2|]. split; [exact Hp3|].
    split; [rewrite (KP 21%bv) by in_tac; exact R21|].
    split; [rewrite (KP 24%bv) by in_tac; exact R24|].
    split; [rewrite (KP 25%bv) by in_tac; exact R25|].
    split; [rewrite (KP 18%bv) by in_tac; exact R18|].
    split; [rewrite (KP 23%bv) by in_tac; exact R23|].
    split; [rewrite (KP 19%bv) by in_tac; exact R19|].
    split; [rewrite (KP 26%bv) by in_tac; exact R26|].
    rewrite (KP 27%bv) by in_tac; exact R27.
Qed.

(* 0x8110c -> the call of check_groupa at 0x8118c: one parameter of one channel. *)
Lemma g1_in : forall POST cx fp k acc ly3 S3 W3 (ms3 : machine_state) md3 t s c p,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  YG01.frames S3 = [(GE_CID, fp)] ->
  mo_le MT (c_S cx) S3 acc ->
  g1_at GPS_g1in cx fp k acc ly3 S3 W3 ms3 t s c p ->
  g1_K POST GPS_g1cg cx fp k acc t s c p ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros POST cx fp k acc ly3 S3 W3 ms3 md3 t s c p HB HJ Hfrm Hmo HG K.
  pose proof HG as HG0.
  destruct HG as (HBD & Hk & Hacc & HBLK & HROWS & Hc1 & Hc2 & Hp3 & R21 & R24 & R25 & R18 & R23
    & R19 & R26 & R27).
  pose proof HBD as (Hpc & Hrv & Hsv & Hrom & Hfrg & Hfcsr & (G2 & G8 & G9 & G3 & G4) & HSAV & HSHD
    & HFL & HLEN & HINP).
  pose proof HBLK as (Hab & Hins & HTAB & HWS & HST & HREL & HI1 & HSL & HS88 & HS120 & HS96 & HS64
    & R20 & Hcn & Htpos & Hspos & HAB).
  pose proof HTAB as (Hint & _ & HTl & _).
  pose proof HROWS as (Hok & Hwant & HSW).
  pose proof HSL as (HSLM & HS8 & _).
  pose proof HSLM as (_ & _ & _ & _ & HS136 & HS144 & HS152 & HS176).
  destruct (gsw_bounds B MT cx fp k ly3 S3 W3 (ms_mem ms3) md3 t s HB HJ Hfrm Hint Hins LAWS)
    as (Hal & Hsp0 & H47 & Hsp1 & Hsp32 & HF0 & HFc & HF32 & Ht4096 & Htc & Hs4096 & Hsc & HPB).
  unfold GE_STK in Hsp0.
  destruct (gsw_base_facts B MT cx HB) as (HPRE & HROD & _ & _).
  pose proof (@alloc_ceiling_value rc) as HAC.
  pose proof (g1_ok_bounds (c_pl cx) Hok) as (Hb0 & Hin1 & Hin40 & Hbw).
  pose proof (g1_frame_app LAWS cx fp k ly3 S3 W3 (ms_mem ms3) md3 HJ Hfrm) as HAPP.
  pose proof (sw_mbytes_ge (c_pl cx)) as Hsm.
  pose proof (sw_bytes_len cx t Hok Hwant) as Hswl.
  pose proof (eq_refl : GO_A = 448) as HA448.
  pose proof (eq_refl : GO_WAS = 32) as HW32.
  pose proof (eq_refl : GO_SET = 240) as HS240.
  rewrite Hok in HAB. cbv iota in HAB. destruct HAB as (HA0 & HA1).
  remember (sw_base (c_pl cx) + Z.of_nat c) as ch eqn:Hch_eq.
  remember (g1_i ch p) as iw eqn:Hiw_eq.
  assert (Hch : 0 <= ch < 48) by (rewrite Hch_eq; lia).
  assert (Hiw : 0 <= iw < 144) by (rewrite Hiw_eq; unfold g1_i; lia).
  pose proof (g1_tb_range (ws_end (c_pl cx)) iw) as Hwv.
  pose proof (g1_tb_range (st_end (c_pl cx)) iw) as Hsv2.
  (* the two cells of the frame this turn reads *)
  assert (HWSv : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms3)) (gF cx fp + GO_WAS + iw) 1
                   (tb (ws_end (c_pl cx)) iw)).
  { unfold gfarr in HWS.
    destruct (garr8_nthZ SEGS (mrestrict (w_H W3) (ms_mem ms3)) (gF cx fp + GO_WAS)
      (map (fun b : byte => bv_unsigned b) (ws_end (c_pl cx))) iw HWS ltac:(lia)
      ltac:(rewrite length_map, length_ws_end; lia)) as [Hv _].
    rewrite g1_nth_map_bu in Hv. exact Hv. }
  assert (HSTv : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms3)) (gF cx fp + GO_SET + iw) 1
                   (tb (st_end (c_pl cx)) iw)).
  { unfold gfarr in HST.
    destruct (garr8_nthZ SEGS (mrestrict (w_H W3) (ms_mem ms3)) (gF cx fp + GO_SET)
      (map (fun b : byte => bv_unsigned b) (st_end (c_pl cx))) iw HST ltac:(lia)
      ltac:(rewrite length_map, length_st_end; lia)) as [Hv _].
    rewrite g1_nth_map_bu in Hv. exact Hv. }
  assert (HAv : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms3)) (gF cx fp + GO_A) 1
                  (sw_base (c_pl cx)))
    by exact (proj1 (val_mem1_of_aview SEGS (w_H W3) (ms_mem ms3) _ _ HA0)).
  assert (HAv1 : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms3)) (gF cx fp + GO_A + 1) 1
                   (sw_in (c_pl cx))).
  { replace (gF cx fp + GO_A + 1) with (gF cx fp + (GO_A + 1)) by lia.
    exact (proj1 (val_mem1_of_aview SEGS (w_H W3) (ms_mem ms3) _ _ HA1)). }
  (* the environment of the run *)
  pose proof (env_agree_Eimg (ms_regs ms3) (g1_ex cx fp s ch iw)) as HAE.
  pose proof (regs_ok_Eimg_Ereg (ms_regs ms3) (g1_ex cx fp s ch iw)) as HREG.
  pose proof (Eimg_env (Ereg (ms_regs ms3) (g1_ex cx fp s ch iw))) as HEI.
  assert (XR : forall n (r : bv 5), Z.of_nat n = bv_unsigned r ->
    ew (Eimg (Ereg (ms_regs ms3) (g1_ex cx fp s ch iw))) n = getr (ms_regs ms3) r)
    by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (X32 : ew (Eimg (Ereg (ms_regs ms3) (g1_ex cx fp s ch iw))) 32 = w64 (sw_base (c_pl cx)))
    by (rewrite Eimg_low by (unfold A_TEXT; lia); unfold g1_ex; reflexivity).
  assert (X33 : ew (Eimg (Ereg (ms_regs ms3) (g1_ex cx fp s ch iw))) 33 = w64 (sw_in (c_pl cx)))
    by (rewrite Eimg_low by (unfold A_TEXT; lia); unfold g1_ex; reflexivity).
  assert (X34 : ew (Eimg (Ereg (ms_regs ms3) (g1_ex cx fp s ch iw))) 34 = w64 s)
    by (rewrite Eimg_low by (unfold A_TEXT; lia); unfold g1_ex; reflexivity).
  assert (X35 : ew (Eimg (Ereg (ms_regs ms3) (g1_ex cx fp s ch iw))) 35 = w64 (gF cx fp + GO_SET))
    by (rewrite Eimg_low by (unfold A_TEXT; lia); unfold g1_ex; reflexivity).
  assert (X36 : ew (Eimg (Ereg (ms_regs ms3) (g1_ex cx fp s ch iw))) 36 = w64 ch)
    by (rewrite Eimg_low by (unfold A_TEXT; lia); unfold g1_ex; reflexivity).
  assert (X37 : ew (Eimg (Ereg (ms_regs ms3) (g1_ex cx fp s ch iw))) 37 = w64 (gF cx fp + GO_WAS))
    by (rewrite Eimg_low by (unfold A_TEXT; lia); unfold g1_ex; reflexivity).
  assert (X38 : ew (Eimg (Ereg (ms_regs ms3) (g1_ex cx fp s ch iw))) 38
                = w64 (gF cx fp + GO_WAS + iw))
    by (rewrite Eimg_low by (unfold A_TEXT; lia); unfold g1_ex; reflexivity).
  assert (X39 : ew (Eimg (Ereg (ms_regs ms3) (g1_ex cx fp s ch iw))) 39
                = w64 (tb (ws_end (c_pl cx)) iw))
    by (rewrite Eimg_low by (unfold A_TEXT; lia); unfold g1_ex; reflexivity).
  assert (X40 : ew (Eimg (Ereg (ms_regs ms3) (g1_ex cx fp s ch iw))) 40
                = w64 (gF cx fp + GO_SET + iw))
    by (rewrite Eimg_low by (unfold A_TEXT; lia); unfold g1_ex; reflexivity).
  assert (X41 : ew (Eimg (Ereg (ms_regs ms3) (g1_ex cx fp s ch iw))) 41
                = w64 (tb (st_end (c_pl cx)) iw))
    by (rewrite Eimg_low by (unfold A_TEXT; lia); unfold g1_ex; reflexivity).
  remember (Eimg (Ereg (ms_regs ms3) (g1_ex cx fp s ch iw))) as E eqn:HE. clear HE.
  assert (E2 : ew E 2 = w64 (c_sp1 cx))
    by (transitivity (getr (ms_regs ms3) 2); [apply XR; reflexivity | exact G2]).
  assert (E9 : ew E 9 = w64 (c_sp1 cx))
    by (transitivity (getr (ms_regs ms3) 9); [apply XR; reflexivity | exact G9]).
  assert (E18 : ew E 18 = w64 (gF cx fp + GO_A))
    by (transitivity (getr (ms_regs ms3) 18); [apply XR; reflexivity | exact R18]).
  assert (E21 : ew E 21 = w64 (Z.of_nat c))
    by (transitivity (getr (ms_regs ms3) 21); [apply XR; reflexivity | exact R21]).
  assert (E24 : ew E 24 = w64 (Z.of_nat c))
    by (transitivity (getr (ms_regs ms3) 24); [apply XR; reflexivity | exact R24]).
  assert (E26 : ew E 26 = w64 (Z.of_nat p))
    by (transitivity (getr (ms_regs ms3) 26); [apply XR; reflexivity | exact R26]).
  assert (E27 : ew E 27 = w64 (g1_row s c p))
    by (transitivity (getr (ms_regs ms3) 27); [apply XR; reflexivity | exact R27]).
  assert (E20 : ew E 20 = w64 t)
    by (transitivity (getr (ms_regs ms3) 20); [apply XR; reflexivity | exact R20]).
  (* the seat *)
  rewrite (ms_shape ms3 (BASE + GPS_g1in) Hpc Hrv Hsv Hrom Hfrg Hfcsr).
  assert (HS : st_ok_pi SEGS VAL E ss_g1
    (restrict (w_H W3) (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + GPS_g1in)) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_g1. apply pa_entry_st_ok_full.
    - exact HREG.
    - vm_compute. reflexivity.
    - unfold g1_regions.
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
      + apply (g1_regionA E _ (gF cx fp + GO_A) (sw_base (c_pl cx)) (sw_in (c_pl cx)) E18 X32 X33);
        first [lia | exact HAv | exact HAv1].
      + apply (g1_regionS E W3 ms3 cx s (gF cx fp + GO_SET) (gF cx fp + GO_WAS) E9 X34 X35 X37);
        first [lia | exact HS64 | exact HS136 | exact HS144 | exact HS152].
      + apply (g1_region1 E _ 38%nat 39%nat (gF cx fp + GO_WAS + iw) (tb (ws_end (c_pl cx)) iw)
          X38 X39); first [lia | exact HWSv].
      + apply (g1_region1 E _ 40%nat 41%nat (gF cx fp + GO_SET + iw) (tb (st_end (c_pl cx)) iw)
          X40 X41); first [lia | exact HSTv].
    - unfold g1_regions, g1_RA, g1_RS, g1_R1.
      cbn [YP09.pairwise_disjoint YP09.all_disjoint].
      unfold extent_disjoint, base_val.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite E18, E9, X38, X40. unfold w64. rewrite !unsigned_lit_small by lia.
      repeat split; first [left; lia | right; lia].
    - split; [| split; [exact I |]].
      + unfold g1_atoms. cbn [atoms_ok].
        split; [exact (g1_afact E 32%nat 0 255 _ X32 ltac:(lia) ltac:(lia) ltac:(lia))|].
        split; [exact (g1_afact E 33%nat 0 255 _ X33 ltac:(lia) ltac:(lia) ltac:(lia))|].
        split; [exact (g1_afact E 36%nat 0 255 _ X36 ltac:(lia) ltac:(lia) ltac:(lia))|].
        split; [exact (g1_afact E 38%nat 4096 0x7fffff800000 _ X38 ltac:(lia) ltac:(lia) ltac:(lia))|].
        split; [exact (g1_afact E 39%nat 0 255 _ X39 ltac:(lia) ltac:(lia) ltac:(lia))|].
        split; [exact (g1_afact E 40%nat 4096 0x7fffff800000 _ X40 ltac:(lia) ltac:(lia) ltac:(lia))|].
        split; [exact (g1_afact E 41%nat 0 255 _ X41 ltac:(lia) ltac:(lia) ltac:(lia)) | exact I].
      + unfold g1_alias. cbn [alias_ok].
        split; [exact (g1_alias_add E 24%nat 32%nat 36%nat (Z.of_nat c) (sw_base (c_pl cx))
                 E24 X32 ltac:(rewrite X36, Hch_eq; f_equal; lia) ltac:(lia) ltac:(lia) ltac:(lia))|].
        split; [exact (g1_alias_add E 32%nat 21%nat 36%nat (sw_base (c_pl cx)) (Z.of_nat c)
                 X32 E21 ltac:(rewrite X36, Hch_eq; f_equal; lia) ltac:(lia) ltac:(lia) ltac:(lia))|].
        split; [exact (g1_alias_and E 36%nat ch X36 ltac:(lia))|].
        split; [exact (g1_alias_and E 26%nat (Z.of_nat p) E26 ltac:(lia))|].
        split; [exact (g1_alias_idx E 37%nat 38%nat (gF cx fp + GO_WAS) ch p X37 X36 E26
                 ltac:(rewrite X38, Hiw_eq; unfold g1_i; f_equal; lia)
                 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))|].
        split; [exact (g1_alias_idx E 35%nat 40%nat (gF cx fp + GO_SET) ch p X35 X36 E26
                 ltac:(rewrite X40, Hiw_eq; unfold g1_i; f_equal; lia)
                 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) | exact I]. }
  assert (SHOK : sh_ok SEGS Bx3 g1_SH E (mrestrict (w_H W3) (ms_mem ms3))).
  { unfold sh_ok, g1_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    - apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E Bx3 38%nat (gF cx fp + GO_WAS + iw) 1
        (gF cx fp + GO_WAS + iw) 0 1).
      + apply (g1_cell_addressable cx fp W3 ms3 GO_WAS iw HSHD HF32 HF0 HFc); [left; reflexivity | lia].
      + unfold Bx3, SB3. rewrite U_SLit. reflexivity.
      + apply (U_atom E 38%nat); [exact X38 | lia].
      + lia.
      + lia.
      + intros x Hx. revert HAPP Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL.
        intros. lia.
    - apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E Bx3 40%nat (gF cx fp + GO_SET + iw) 1
        (gF cx fp + GO_SET + iw) 0 1).
      + apply (g1_cell_addressable cx fp W3 ms3 GO_SET iw HSHD HF32 HF0 HFc); [right; reflexivity | lia].
      + unfold Bx3, SB3. rewrite U_SLit. reflexivity.
      + apply (U_atom E 40%nat); [exact X40 | lia].
      + lia.
      + lia.
      + intros x Hx. revert HAPP Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL.
        intros. lia. }
  (* the run to the test of was_set[i], 0x81144 *)
  paj_run_tok RUN HS HJ SHOK Bsp3; [awr_ok_tac |].
  g1_mem HF HM1. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK Bsp3.
  - (* was_set[i] = 0: the value is reac_headamp_default(p) *)
    rewrite branch_eq_U in Hc.
    rewrite (U_atom _ 39%nat (tb (ws_end (c_pl cx)) iw)) in Hc;
      [| cbn [ew ewset Nat.eqb]; exact X39 | lia].
    rewrite (U_lit _ 0) in Hc by lia.
    apply Z.eqb_eq in Hc.
    (* on to the call of reac_headamp_default at 0x81170 *)
    paj_run_tok RUN HS HJ SHOK Bsp3; [awr_ok_tac |].
    g1_mem HF HM2. clear HF HFr HG.
    pmkst HS.
    prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp.
    prreg HS (4%bv : bv 5) Rtp. prreg HS (8%bv : bv 5) Rs0. prreg HS (10%bv : bv 5) Ra0.
    prreg HS (20%bv : bv 5) R20'. prreg HS (21%bv : bv 5) R21'. prreg HS (22%bv : bv 5) R22'.
    prreg HS (23%bv : bv 5) R23'. prreg HS (24%bv : bv 5) R24'. prreg HS (25%bv : bv 5) R25'.
    prreg HS (26%bv : bv 5) R26'. prreg HS (27%bv : bv 5) R27'. prreg HS (18%bv : bv 5) R18'.
    prreg HS (19%bv : bv 5) R19'.
    rewrite E2 in Rsp. rewrite E26 in Ra0. rewrite E20 in R20'. rewrite E21 in R21'.
    rewrite X32 in R22'. rewrite E26 in R26'. rewrite E27 in R27'. rewrite E18 in R18'.
    rewrite E24 in R24'.
    eapply SRr_bind.
    { apply (gsw_hdflt B MT LAWS THD cx fp k ly3 S3 W3 _ _ _ GPS_g1hd (Z.of_nat p) HB HJ).
      - exact Rsp.
      - rewrite Rgp. rewrite (XR 3%nat 3%bv eq_refl). exact G3.
      - rewrite Rtp. rewrite (XR 4%nat 4%bv eq_refl). exact G4.
      - rewrite Rs0. rewrite (XR 8%nat 8%bv eq_refl). exact G8.
      - exact Rra.
      - unfold GPS_g1hd. lia.
      - reflexivity.
      - rewrite HM2, HM1. exact (proj1 (g1_saved cx W3 ms3 HSAV)).
      - rewrite HM2, HM1. exact (proj2 (g1_saved cx W3 ms3 HSAV)).
      - exact Ra0.
      - lia. }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hd2 & HM3).
    (* 0x81174 -> the call of check_groupa at 0x8118c *)
    pose proof (regs_ok_Eimg_Ereg regs2 [w64 ch]) as HREG2.
    pose proof (Eimg_env (Ereg regs2 [w64 ch])) as HEI2.
    assert (XR2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r ->
      ew (Eimg (Ereg regs2 [w64 ch])) n = getr regs2 r)
      by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
    assert (Y32 : ew (Eimg (Ereg regs2 [w64 ch])) 32 = w64 ch)
      by (rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
    remember (Eimg (Ereg regs2 [w64 ch])) as EB eqn:HEB. clear HEB.
    assert (F22 : ew EB 22 = w64 (sw_base (c_pl cx))).
    { rewrite (XR2 22%nat 22%bv eq_refl). apg HP2 (22%bv : bv 5) 22. exact R22'. }
    assert (F21 : ew EB 21 = w64 (Z.of_nat c)).
    { rewrite (XR2 21%nat 21%bv eq_refl). apg HP2 (21%bv : bv 5) 21. exact R21'. }
    assert (F26 : ew EB 26 = w64 (Z.of_nat p)).
    { rewrite (XR2 26%nat 26%bv eq_refl). apg HP2 (26%bv : bv 5) 26. exact R26'. }
    assert (HS2 : st_ok_pi SEGS VAL EB ss_g1hd
      (restrict (w_H W3) (mkst regs2 (Z_to_bv 64 (BASE + GPS_g1hd)) mem2 (seg_rom SEGS)))).
    { rewrite restrict_mkst_fx. unfold ss_g1hd. apply pa_entry_st_ok_full.
      - exact HREG2.
      - vm_compute. reflexivity.
      - apply Forall_nil.
      - exact I.
      - split; [| split; [exact I |]].
        + cbn [f_atoms atoms_ok].
          split; [exact (g1_afact EB 32%nat 0 255 ch Y32 ltac:(lia) ltac:(lia) ltac:(lia)) | exact I].
        + cbn [f_alias alias_ok].
          split; [exact (g1_alias_add EB 22%nat 21%nat 32%nat (sw_base (c_pl cx)) (Z.of_nat c) F22 F21
                   ltac:(rewrite Y32, Hch_eq; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia))|].
          split; [exact (g1_alias_and EB 32%nat ch Y32 ltac:(lia))|].
          split; [exact (g1_alias_and EB 26%nat (Z.of_nat p) F26 ltac:(lia)) | exact I]. }
    assert (SHOK2 : sh_ok SEGS Bx3 [] EB (mrestrict (w_H W3) mem2)) by constructor.
    paj_run_tok RUN HS2 HJ2 SHOK2 Bsp3; [awr_ok_tac |].
    g1_mem HF HM4. clear HF HFr HG.
    pmkst HS2.
    apply (g1_call POST cx fp k acc ly3 S3 W3 ms3 _ _ _ t s c p HB HJ2 Hfrm Hmo HG0).
    + intros x. rewrite HM4, HM3, HM2, HM1. reflexivity.
    + intros r Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<-|Hr]; [g1_rk2 HS2 XR2 HP2 HS XR |]). destruct Hr.
    + prreg HS2 (1%bv : bv 5) Rra2. exact Rra2.
    + prreg HS2 (10%bv : bv 5) Rb. rewrite Rb, (XR2 27%nat 27%bv eq_refl).
      apg HP2 (27%bv : bv 5) 27. exact R27'.
    + prreg HS2 (11%bv : bv 5) Rb. rewrite Rb, Y32, Hch_eq. reflexivity.
    + prreg HS2 (12%bv : bv 5) Rb. rewrite Rb. exact F26.
    + prreg HS2 (13%bv : bv 5) Rb. rewrite Rb, (XR2 20%nat 20%bv eq_refl).
      apg HP2 (20%bv : bv 5) 20. exact R20'.
    + prreg HS2 (14%bv : bv 5) Rb. rewrite Rb, (XR2 10%nat 10%bv eq_refl), Hd2.
      rewrite <- Hch_eq, (g1_want_eff (c_pl cx) t ch p Htpos Hp3 Hch HREL).
      rewrite Hiw_eq in Hc. unfold g1_i in Hc. rewrite Hc. reflexivity.
    + exact K.
  - (* was_set[i] <> 0: the value is set_to[i] *)
    rewrite branch_eq_U in Hc.
    rewrite (U_atom _ 39%nat (tb (ws_end (c_pl cx)) iw)) in Hc;
      [| cbn [ew ewset Nat.eqb]; exact X39 | lia].
    rewrite (U_lit _ 0) in Hc by lia.
    apply Z.eqb_neq in Hc.
    (* on to the call of check_groupa at 0x8118c *)
    paj_run_tok RUN HS HJ SHOK Bsp3; [awr_ok_tac |].
    g1_mem HF HM2. clear HF HFr HG.
    pmkst HS.
    apply (g1_call POST cx fp k acc ly3 S3 W3 ms3 _ _ _ t s c p HB HJ Hfrm Hmo HG0).
    + intros x. rewrite HM2, HM1. reflexivity.
    + intros r Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<-|Hr]; [g1_rk HS XR |]). destruct Hr.
    + prreg HS (1%bv : bv 5) Rra. exact Rra.
    + prreg HS (10%bv : bv 5) Rb. rewrite Rb. exact E27.
    + prreg HS (11%bv : bv 5) Rb. rewrite Rb, X36, Hch_eq. reflexivity.
    + prreg HS (12%bv : bv 5) Rb. rewrite Rb. exact E26.
    + prreg HS (13%bv : bv 5) Rb. rewrite Rb. exact E20.
    + prreg HS (14%bv : bv 5) Rb. rewrite Rb, X41.
      rewrite <- Hch_eq, (g1_want_eff (c_pl cx) t ch p Htpos Hp3 Hch HREL).
      rewrite Hiw_eq in Hc. unfold g1_i in Hc.
      rewrite (proj2 (Z.eqb_neq _ _) Hc). rewrite Hiw_eq. reflexivity.
    + exact K.
Qed.

(* 0x81190 -> the head of the parameter loop, the head of the channel loop, or
   0x811f8: the two loop tests and the block that sets the group-B loop up. *)
Lemma g1_cg : forall POST cx fp k acc ly3 S3 W3 (ms3 : machine_state) md3 t s c p,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  YG01.frames S3 = [(GE_CID, fp)] ->
  mo_le MT (c_S cx) S3 acc ->
  g1_at GPS_g1cg cx fp k acc ly3 S3 W3 ms3 t s c p ->
  ((S p < 3)%nat -> g1_K POST GPS_g1in cx fp k acc t s c (S p)) ->
  (forall ly4 S4 W4 (ms4 : machine_state) md4,
     ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
       [(GE_CID, fp)] ly4 S4 W4 (ms_mem ms4) md4 k ->
     YG01.frames S4 = [(GE_CID, fp)] -> mo_le MT (c_S cx) S4 acc ->
     GIS_ga1 B MT cx fp k acc ly4 S4 W4 ms4 md4 ->
     getr (ms_regs ms4) 21 = w64 (Z.of_nat c + 1) ->
     SRr SEGS W4 (mkCfg ms4 md4) (POST cx)) ->
  ge_from B MT POST (GIS_gbhd B MT) ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros POST cx fp k acc ly3 S3 W3 ms3 md3 t s c p HB HJ Hfrm Hmo HG INNER OUTC NEXT.
  pose proof HG as HG0.
  destruct HG as (HBD & Hk & Hacc & HBLK & HROWS & Hc1 & Hc2 & Hp3 & R21 & R24 & R25 & R18 & R23
    & R19 & R26 & R27).
  pose proof HBD as (Hpc & Hrv & Hsv & Hrom & Hfrg & Hfcsr & (G2 & G8 & G9 & G3 & G4) & HSAV & HSHD
    & HFL & HLEN & HINP).
  pose proof HBLK as (Hab & Hins & HTAB & HWS & HST & HREL & HI1 & HSL & HS88 & HS120 & HS96 & HS64
    & R20 & Hcn & Htpos & Hspos & HAB).
  pose proof HTAB as (Hint & _ & HTl & _).
  pose proof HROWS as (Hok & Hwant & HSW).
  pose proof HSL as (HSLM & HS8 & _).
  destruct (gsw_bounds B MT cx fp k ly3 S3 W3 (ms_mem ms3) md3 t s HB HJ Hfrm Hint Hins LAWS)
    as (Hal & Hsp0 & H47 & Hsp1 & Hsp32 & HF0 & HFc & HF32 & Ht4096 & Htc & Hs4096 & Hsc & HPB).
  unfold GE_STK in Hsp0.
  pose proof (@alloc_ceiling_value rc) as HAC.
  pose proof (g1_ok_bounds (c_pl cx) Hok) as (Hb0 & Hin1 & Hin40 & Hbw).
  pose proof (eq_refl : GO_A = 448) as HA448.
  pose proof (eq_refl : GO_POLL = 464) as HP464.
  pose proof (sw_mbytes_ge (c_pl cx)) as Hsm.
  rewrite Hok in HAB. cbv iota in HAB. destruct HAB as (HA0 & HA1).
  assert (HAv : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms3)) (gF cx fp + GO_A) 1
                  (sw_base (c_pl cx)))
    by exact (proj1 (val_mem1_of_aview SEGS (w_H W3) (ms_mem ms3) _ _ HA0)).
  assert (HAv1 : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms3)) (gF cx fp + GO_A + 1) 1
                   (sw_in (c_pl cx))).
  { replace (gF cx fp + GO_A + 1) with (gF cx fp + (GO_A + 1)) by lia.
    exact (proj1 (val_mem1_of_aview SEGS (w_H W3) (ms_mem ms3) _ _ HA1)). }
  pose proof (regs_ok_Eimg_Ereg (ms_regs ms3)
    [w64 (sw_base (c_pl cx)); w64 (sw_in (c_pl cx)); w64 (gF cx fp + GO_POLL); w64 s]) as HREGC.
  pose proof (Eimg_env (Ereg (ms_regs ms3)
    [w64 (sw_base (c_pl cx)); w64 (sw_in (c_pl cx)); w64 (gF cx fp + GO_POLL); w64 s])) as HEI.
  assert (XR : forall n (r : bv 5), Z.of_nat n = bv_unsigned r ->
    ew (Eimg (Ereg (ms_regs ms3)
      [w64 (sw_base (c_pl cx)); w64 (sw_in (c_pl cx)); w64 (gF cx fp + GO_POLL); w64 s])) n
      = getr (ms_regs ms3) r)
    by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (Y32 : ew (Eimg (Ereg (ms_regs ms3)
    [w64 (sw_base (c_pl cx)); w64 (sw_in (c_pl cx)); w64 (gF cx fp + GO_POLL); w64 s])) 32
    = w64 (sw_base (c_pl cx)))
    by (rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
  assert (Y33 : ew (Eimg (Ereg (ms_regs ms3)
    [w64 (sw_base (c_pl cx)); w64 (sw_in (c_pl cx)); w64 (gF cx fp + GO_POLL); w64 s])) 33
    = w64 (sw_in (c_pl cx)))
    by (rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
  assert (Y34 : ew (Eimg (Ereg (ms_regs ms3)
    [w64 (sw_base (c_pl cx)); w64 (sw_in (c_pl cx)); w64 (gF cx fp + GO_POLL); w64 s])) 34
    = w64 (gF cx fp + GO_POLL))
    by (rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
  assert (Y35 : ew (Eimg (Ereg (ms_regs ms3)
    [w64 (sw_base (c_pl cx)); w64 (sw_in (c_pl cx)); w64 (gF cx fp + GO_POLL); w64 s])) 35
    = w64 s)
    by (rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
  remember (Eimg (Ereg (ms_regs ms3)
    [w64 (sw_base (c_pl cx)); w64 (sw_in (c_pl cx)); w64 (gF cx fp + GO_POLL); w64 s])) as EC
    eqn:HEC. clear HEC.
  assert (Y2 : ew EC 2 = w64 (c_sp1 cx))
    by (transitivity (getr (ms_regs ms3) 2); [apply XR; reflexivity | exact G2]).
  assert (Y9 : ew EC 9 = w64 (c_sp1 cx))
    by (transitivity (getr (ms_regs ms3) 9); [apply XR; reflexivity | exact G9]).
  assert (Y18 : ew EC 18 = w64 (gF cx fp + GO_A))
    by (transitivity (getr (ms_regs ms3) 18); [apply XR; reflexivity | exact R18]).
  assert (Y19 : ew EC 19 = w64 (gSH cx fp))
    by (transitivity (getr (ms_regs ms3) 19); [apply XR; reflexivity | exact R19]).
  assert (Y20 : ew EC 20 = w64 t)
    by (transitivity (getr (ms_regs ms3) 20); [apply XR; reflexivity | exact R20]).
  assert (Y21 : ew EC 21 = w64 (Z.of_nat c))
    by (transitivity (getr (ms_regs ms3) 21); [apply XR; reflexivity | exact R21]).
  assert (Y23 : ew EC 23 = w64 3)
    by (transitivity (getr (ms_regs ms3) 23); [apply XR; reflexivity | exact R23]).
  assert (Y24 : ew EC 24 = w64 (Z.of_nat c))
    by (transitivity (getr (ms_regs ms3) 24); [apply XR; reflexivity | exact R24]).
  assert (Y25 : ew EC 25 = w64 (s + 374 + 102 * (Z.of_nat c - 1)))
    by (transitivity (getr (ms_regs ms3) 25); [apply XR; reflexivity | exact R25]).
  assert (Y26 : ew EC 26 = w64 (Z.of_nat p))
    by (transitivity (getr (ms_regs ms3) 26); [apply XR; reflexivity | exact R26]).
  assert (Y27 : ew EC 27 = w64 (g1_row s c p))
    by (transitivity (getr (ms_regs ms3) 27); [apply XR; reflexivity | exact R27]).
  rewrite (ms_shape ms3 (BASE + GPS_g1cg) Hpc Hrv Hsv Hrom Hfrg Hfcsr).
  assert (HS : st_ok_pi SEGS VAL EC ss_g1cg
    (restrict (w_H W3) (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + GPS_g1cg)) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_g1cg. apply pa_entry_st_ok_full.
    - exact HREGC.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + apply (g1_regionA EC _ (gF cx fp + GO_A) (sw_base (c_pl cx)) (sw_in (c_pl cx)) Y18 Y32 Y33);
        first [lia | exact HAv | exact HAv1].
      + apply (g1_regionS2 EC W3 ms3 cx (gF cx fp + GO_POLL) s Y9 Y34 Y35);
        first [lia | exact HS8 | exact HS64].
    - unfold g1_RA, g1_RS2.
      cbn [YP09.pairwise_disjoint YP09.all_disjoint].
      unfold extent_disjoint, base_val.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite Y18, Y9. unfold w64. rewrite !unsigned_lit_small by lia.
      repeat split; first [left; lia | right; lia].
    - split; [| split; [exact I |]].
      + cbn [f_atoms atoms_ok].
        split; [exact (g1_afact EC 21%nat 1 40 _ Y21 ltac:(lia) ltac:(lia) ltac:(lia))|].
        split; [exact (g1_afact EC 33%nat 0 255 _ Y33 ltac:(lia) ltac:(lia) ltac:(lia)) | exact I].
      + cbn [f_alias alias_ok]. exact I. }
  assert (SHOK : sh_ok SEGS Bx3 [] EC (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  (* the test of the parameter loop at 0x81198 *)
  paj_run_tok RUN HS HJ SHOK Bsp3; [awr_ok_tac |].
  g1_mem HF HM1. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK Bsp3.
  - (* p + 1 < 3: the next parameter *)
    rewrite branch_ne_U in Hc.
    rewrite (U_atom_off _ 26%nat (Z.of_nat p) 1) in Hc; [| cbn [ew ewset Nat.eqb]; exact Y26 | lia | lia].
    rewrite (U_atom _ 23%nat 3) in Hc; [| cbn [ew ewset Nat.eqb]; exact Y23 | lia].
    apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bsp3 GPS_g1in; [awr_ok_tac |].
    g1_mem HF HM2. clear HF HFr HG.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg ?msf ?mdf) _ =>
      apply (INNER ltac:(lia) ly3 S3 W3 msf mdf HJ Hfrm Hmo) end.
    unfold g1_at. cbn [ms_regs ms_mem mkst].
    split.
    { apply (ge_body_move cx fp GPS_g1cg GPS_g1in W3 W3 ms3 _ _ GSH_a HBD).
      - apply vkeep_mem. intros x. rewrite HM2, HM1. reflexivity.
      - lia.
      - g1_rk HS XR.
      - g1_rk HS XR.
      - g1_rk HS XR.
      - g1_rk HS XR.
      - g1_rk HS XR. }
    split; [exact Hk|]. split; [exact Hacc|].
    split.
    { eapply gsw_blk_move; [exact HBLK | reflexivity | | lia |].
      - apply vkeep_mem. intros x. cbn [ms_mem mkst]. rewrite HM2, HM1. reflexivity.
      - cbn [ms_regs mkst]. g1_rk HS XR. }
    split.
    { eapply (gsw_rows_move cx fp); [exact HROWS |].
      apply vkeep_mem. intros x. cbn [ms_mem mkst]. rewrite HM2, HM1. reflexivity. }
    split; [exact Hc1|]. split; [exact Hc2|]. split; [lia|].
    split; [prreg HS (21%bv : bv 5) Rb; rewrite Rb, Y21; reflexivity|].
    split; [prreg HS (24%bv : bv 5) Rb; rewrite Rb, Y24; reflexivity|].
    split; [prreg HS (25%bv : bv 5) Rb; rewrite Rb, Y25; reflexivity|].
    split; [prreg HS (18%bv : bv 5) Rb; rewrite Rb, Y18; reflexivity|].
    split; [prreg HS (23%bv : bv 5) Rb; rewrite Rb, Y23; reflexivity|].
    split; [prreg HS (19%bv : bv 5) Rb; rewrite Rb, Y19; reflexivity|].
    split.
    { prreg HS (26%bv : bv 5) Rb. rewrite Rb, Y26. unfold w64.
      rewrite unsigned_lit_small by lia. f_equal; lia. }
    prreg HS (27%bv : bv 5) Rb. rewrite Rb, Y27. unfold w64, g1_row.
    rewrite unsigned_lit_small by lia. f_equal; lia.
  - (* p + 1 = 3: the test of the channel loop at 0x811c8 *)
    rewrite branch_ne_U in Hc.
    rewrite (U_atom_off _ 26%nat (Z.of_nat p) 1) in Hc; [| cbn [ew ewset Nat.eqb]; exact Y26 | lia | lia].
    rewrite (U_atom _ 23%nat 3) in Hc; [| cbn [ew ewset Nat.eqb]; exact Y23 | lia].
    apply negb_false_iff, Z.eqb_eq in Hc.
    paj_run_tok RUN HS HJ SHOK Bsp3; [awr_ok_tac |].
    g1_mem HF HM2. clear HF HFr HG.
    psrr_branch_tok RUN BR HS SHOK Bsp3.
    + (* c + 1 < a.in: the next channel *)
      rewrite branch_ltu_U in Hc0.
      rewrite (U_atom_off _ 21%nat (Z.of_nat c) 1) in Hc0; [| cbn [ew ewset Nat.eqb]; exact Y21 | lia | lia].
      rewrite (U_atom _ 33%nat (sw_in (c_pl cx))) in Hc0; [| cbn [ew ewset Nat.eqb]; exact Y33 | lia].
      apply Z.ltb_lt in Hc0.
      paj_run_to_tok RUNTO HS HJ SHOK Bsp3 GPS_ga1; [awr_ok_tac |].
      g1_mem HF HM3. clear HF HFr HG.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg ?msf ?mdf) _ =>
        apply (OUTC ly3 S3 W3 msf mdf HJ Hfrm Hmo) end.
      * unfold GIS_ga1. exists t, s, (S c). cbn [ms_regs ms_mem mkst].
        split.
        { apply (ge_body_move cx fp GPS_g1cg GPS_ga1 W3 W3 ms3 _ _ GSH_a HBD).
          - apply vkeep_mem. intros x. rewrite HM3, HM2, HM1. reflexivity.
          - lia.
          - g1_rk HS XR.
          - g1_rk HS XR.
          - g1_rk HS XR.
          - g1_rk HS XR.
          - g1_rk HS XR. }
        split; [exact Hk|]. split; [exact Hacc|].
        split.
        { eapply gsw_blk_move; [exact HBLK | reflexivity | | lia |].
          - apply vkeep_mem. intros x. cbn [ms_mem mkst]. rewrite HM3, HM2, HM1. reflexivity.
          - cbn [ms_regs mkst]. g1_rk HS XR. }
        split.
        { eapply (gsw_rows_move cx fp); [exact HROWS |].
          apply vkeep_mem. intros x. cbn [ms_mem mkst]. rewrite HM3, HM2, HM1. reflexivity. }
        split; [lia|]. split; [lia|].
        split.
        { prreg HS (21%bv : bv 5) Rb. rewrite Rb, Y21. unfold w64.
          rewrite unsigned_lit_small by lia. f_equal; lia. }
        split.
        { prreg HS (24%bv : bv 5) Rb. rewrite Rb, Y24. unfold w64.
          rewrite unsigned_lit_small by lia. f_equal; lia. }
        split.
        { prreg HS (25%bv : bv 5) Rb. rewrite Rb, Y25. unfold w64.
          rewrite unsigned_lit_small by lia. f_equal; lia. }
        split; [prreg HS (18%bv : bv 5) Rb; rewrite Rb, Y18; reflexivity|].
        split; [prreg HS (23%bv : bv 5) Rb; rewrite Rb, Y23; reflexivity|].
        prreg HS (19%bv : bv 5) Rb. rewrite Rb, Y19. reflexivity.
      * cbn [ms_regs mkst]. prreg HS (21%bv : bv 5) Rb. rewrite Rb, Y21. unfold w64.
        rewrite unsigned_lit_small by lia. f_equal; lia.
    + (* a.in <= c + 1: on to the group-B loop *)
      rewrite branch_ltu_U in Hc0.
      rewrite (U_atom_off _ 21%nat (Z.of_nat c) 1) in Hc0; [| cbn [ew ewset Nat.eqb]; exact Y21 | lia | lia].
      rewrite (U_atom _ 33%nat (sw_in (c_pl cx))) in Hc0; [| cbn [ew ewset Nat.eqb]; exact Y33 | lia].
      apply Z.ltb_ge in Hc0.
      paj_run_to_tok RUNTO HS HJ SHOK Bsp3 GPS_gbhd; [awr_ok_tac |].
      g1_mem HF HM3. clear HF HFr HG.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg ?msf ?mdf) _ =>
        apply (NEXT cx fp k acc ly3 S3 W3 msf mdf HB HJ Hfrm Hmo) end.
      unfold GIS_gbhd. exists t, s, 0%nat. cbn [ms_regs ms_mem mkst].
      split.
      { apply (ge_body_move cx fp GPS_g1cg GPS_gbhd W3 W3 ms3 _ _ GSH_a HBD).
        - apply vkeep_mem. intros x. rewrite HM3, HM2, HM1. reflexivity.
        - lia.
        - g1_rk HS XR.
        - g1_rk HS XR.
        - g1_rk HS XR.
        - g1_rk HS XR.
        - g1_rk HS XR. }
      split; [exact Hk|]. split; [exact Hacc|].
      split.
      { eapply gsw_blk_move; [exact HBLK | reflexivity | | lia |].
        - apply vkeep_mem. intros x. cbn [ms_mem mkst]. rewrite HM3, HM2, HM1. reflexivity.
        - cbn [ms_regs mkst]. g1_rk HS XR. }
      split.
      { eapply (gsw_rows_move cx fp); [exact HROWS |].
        apply vkeep_mem. intros x. cbn [ms_mem mkst]. rewrite HM3, HM2, HM1. reflexivity. }
      split; [lia|].
      split; [prreg HS (18%bv : bv 5) Rb; rewrite Rb; reflexivity|].
      split.
      { prreg HS (27%bv : bv 5) Rb. rewrite Rb, Y35. unfold w64.
        rewrite unsigned_lit_small by lia. f_equal; lia. }
      split.
      { prreg HS (26%bv : bv 5) Rb. rewrite Rb.
        rewrite (img_env_atomP EC _ HEI) by (unfold A_TEXT, A_LIM; lia).
        unfold w64. f_equal. change (3 * Z.of_nat 0) with 0. rewrite Z.add_0_r. reflexivity. }
      split; [prreg HS (21%bv : bv 5) Rb; rewrite Rb; reflexivity|].
      split; [prreg HS (19%bv : bv 5) Rb; rewrite Rb, Y34; reflexivity|].
      split; [prreg HS (24%bv : bv 5) Rb; rewrite Rb; reflexivity|].
      split; [prreg HS (25%bv : bv 5) Rb; rewrite Rb; reflexivity|].
      split.
      { prreg HS (23%bv : bv 5) Rb. rewrite Rb. unfold w64. apply bv_eq.
        rewrite !Z_to_bv_unsigned. vm_compute. reflexivity. }
      prreg HS (22%bv : bv 5) Rb. rewrite Rb, Y19. reflexivity.
Qed.

(* The parameter loop, by induction on the parameters left. *)
Lemma g1_inner : forall POST (n : nat) cx fp k acc t s c,
  (forall ly4 S4 W4 (ms4 : machine_state) md4,
     ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
       [(GE_CID, fp)] ly4 S4 W4 (ms_mem ms4) md4 k ->
     YG01.frames S4 = [(GE_CID, fp)] -> mo_le MT (c_S cx) S4 acc ->
     GIS_ga1 B MT cx fp k acc ly4 S4 W4 ms4 md4 ->
     getr (ms_regs ms4) 21 = w64 (Z.of_nat c + 1) ->
     SRr SEGS W4 (mkCfg ms4 md4) (POST cx)) ->
  ge_from B MT POST (GIS_gbhd B MT) ->
  forall p ly3 S3 W3 (ms3 : machine_state) md3, (3 - p = n)%nat ->
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  YG01.frames S3 = [(GE_CID, fp)] ->
  mo_le MT (c_S cx) S3 acc ->
  g1_at GPS_g1in cx fp k acc ly3 S3 W3 ms3 t s c p ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros POST n. induction n as [|n IH]; intros cx fp k acc t s c OUTC NEXT p ly3 S3 W3 ms3 md3
    Hn HB HJ Hfrm Hmo HG.
  { destruct HG as (_ & _ & _ & _ & _ & _ & _ & Hp3 & _). lia. }
  apply (g1_in POST cx fp k acc ly3 S3 W3 ms3 md3 t s c p HB HJ Hfrm Hmo HG).
  intros ly4 S4 W4 ms4 md4 HJ4 Hfr4 Hmo4 HG4.
  apply (g1_cg POST cx fp k acc ly4 S4 W4 ms4 md4 t s c p HB HJ4 Hfr4 Hmo4 HG4).
  - intros Hsp ly5 S5 W5 ms5 md5 HJ5 Hfr5 Hmo5 HG5.
    exact (IH cx fp k acc t s c OUTC NEXT (S p) ly5 S5 W5 ms5 md5 ltac:(lia) HB HJ5 Hfr5 Hmo5 HG5).
  - exact OUTC.
  - exact NEXT.
Qed.

(* The channel loop, by induction on the channels left. The two slots 0x81104 and
   0x81108 set the parameter to 0 and the row pointer to the channel's first row. *)
Lemma g1_outer : forall POST (m : nat),
  ge_from B MT POST (GIS_gbhd B MT) ->
  forall cx fp k acc ly3 S3 W3 (ms3 : machine_state) md3,
  Z.to_nat (sw_in (c_pl cx) - bv_unsigned (getr (ms_regs ms3) 21)) = m ->
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  YG01.frames S3 = [(GE_CID, fp)] ->
  mo_le MT (c_S cx) S3 acc ->
  GIS_ga1 B MT cx fp k acc ly3 S3 W3 ms3 md3 ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros POST m. induction m as [|m IH]; intros NEXT cx fp k acc ly3 S3 W3 ms3 md3 Hm HB HJ Hfrm Hmo HGI;
  destruct HGI as (t & s & c & HBD & Hk & Hacc & HBLK & HROWS & Hc1 & Hc2 & R21 & R24 & R25 & R18
    & R23 & R19);
  pose proof HROWS as (Hok & Hwant & HSW);
  pose proof (g1_ok_bounds (c_pl cx) Hok) as (Hb0 & Hin1 & Hin40 & Hbw);
  rewrite R21 in Hm; unfold w64 in Hm; rewrite unsigned_lit_small in Hm by lia.
  { lia. }
  pose proof HBD as (Hpc & Hrv & Hsv & Hrom & Hfrg & Hfcsr & (G2 & G8 & G9 & G3 & G4) & HSAV & HSHD
    & HFL & HLEN & HINP).
  pose proof HBLK as (Hab & Hins & HTAB & HWS & HST & HREL & HI1 & HSL & HS88 & HS120 & HS96 & HS64
    & R20 & Hcn & Htpos & Hspos & HAB).
  rewrite (ms_shape ms3 (BASE + GPS_ga1) Hpc Hrv Hsv Hrom Hfrg Hfcsr).
  pose proof (plain_entry W3 (ms_regs ms3) (ms_mem ms3) GPS_ga1) as HS.
  pose proof (Eimg_env (Ereg (ms_regs ms3) [])) as HEI.
  assert (XR : forall n (r : bv 5), Z.of_nat n = bv_unsigned r ->
    ew (Eimg (Ereg (ms_regs ms3) [])) n = getr (ms_regs ms3) r)
    by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HE. clear HE.
  assert (E21 : ew E 21 = w64 (Z.of_nat c))
    by (transitivity (getr (ms_regs ms3) 21); [apply XR; reflexivity | exact R21]).
  assert (E24 : ew E 24 = w64 (Z.of_nat c))
    by (transitivity (getr (ms_regs ms3) 24); [apply XR; reflexivity | exact R24]).
  assert (E25 : ew E 25 = w64 (s + 374 + 102 * (Z.of_nat c - 1)))
    by (transitivity (getr (ms_regs ms3) 25); [apply XR; reflexivity | exact R25]).
  assert (E18 : ew E 18 = w64 (gF cx fp + GO_A))
    by (transitivity (getr (ms_regs ms3) 18); [apply XR; reflexivity | exact R18]).
  assert (E23 : ew E 23 = w64 3)
    by (transitivity (getr (ms_regs ms3) 23); [apply XR; reflexivity | exact R23]).
  assert (E19 : ew E 19 = w64 (gSH cx fp))
    by (transitivity (getr (ms_regs ms3) 19); [apply XR; reflexivity | exact R19]).
  assert (E20 : ew E 20 = w64 t)
    by (transitivity (getr (ms_regs ms3) 20); [apply XR; reflexivity | exact R20]).
  assert (SHOK : sh_ok SEGS Bx3 [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  destruct (gsw_bounds B MT cx fp k ly3 S3 W3 (ms_mem ms3) md3 t s HB HJ Hfrm
    (proj1 (proj1 (proj2 (proj2 HBLK)))) Hins LAWS)
    as (Hal & Hsp0 & H47 & Hsp1 & Hsp32 & HF0 & HFc & HF32 & Ht4096 & Htc & Hs4096 & Hsc & HPB).
  unfold GE_STK in Hsp0.
  pose proof (@alloc_ceiling_value rc) as HAC.
  pose proof (sw_mbytes_ge (c_pl cx)) as Hsm.
  paj_run_to_tok RUNTO HS HJ SHOK Bsp3 GPS_g1in; [apply awr_ok_nil |].
  pose proof (frame_of_nil_eq _ _ _ HF) as HM1. cbn [ms_mem mkst] in HM1. clear HF HFr HG.
  pmkst HS.
  apply (g1_inner POST 3%nat cx fp k acc t s c) with (p := 0%nat) (ly3 := ly3) (S3 := S3).
  - (* the next channel, by the induction hypothesis *)
    intros ly4 S4 W4 ms4 md4 HJ4 Hfr4 Hmo4 HGI4 R214.
    apply (IH NEXT cx fp k acc ly4 S4 W4 ms4 md4); try assumption.
    rewrite R214. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact NEXT.
  - reflexivity.
  - exact HB.
  - exact HJ.
  - exact Hfrm.
  - exact Hmo.
  - unfold g1_at. cbn [ms_regs ms_mem mkst].
    split.
    { apply (ge_body_move cx fp GPS_ga1 GPS_g1in W3 W3 ms3 _ _ GSH_a HBD).
      - apply (vkeep_mem (gsw_out0 cx fp)). intros x. rewrite HM1. reflexivity.
      - lia.
      - g1_rk HS XR.
      - g1_rk HS XR.
      - g1_rk HS XR.
      - g1_rk HS XR.
      - g1_rk HS XR. }
    split; [exact Hk|]. split; [exact Hacc|].
    split.
    { eapply gsw_blk_move; [exact HBLK | reflexivity | | lia |].
      - apply (vkeep_mem (gsw_out cx fp t s)). intros x. cbn [ms_mem mkst]. rewrite HM1. reflexivity.
      - cbn [ms_regs mkst]. g1_rk HS XR. }
    split.
    { eapply (gsw_rows_move cx fp); [exact HROWS |].
      apply (vkeep_mem (gsw_out cx fp t s)). intros x. cbn [ms_mem mkst]. rewrite HM1. reflexivity. }
    split; [exact Hc1|]. split; [exact Hc2|]. split; [lia|].
    split; [prreg HS (21%bv : bv 5) Rb; rewrite Rb, E21; reflexivity|].
    split; [prreg HS (24%bv : bv 5) Rb; rewrite Rb, E24; reflexivity|].
    split; [prreg HS (25%bv : bv 5) Rb; rewrite Rb, E25; reflexivity|].
    split; [prreg HS (18%bv : bv 5) Rb; rewrite Rb, E18; reflexivity|].
    split; [prreg HS (23%bv : bv 5) Rb; rewrite Rb, E23; reflexivity|].
    split; [prreg HS (19%bv : bv 5) Rb; rewrite Rb, E19; reflexivity|].
    split; [prreg HS (26%bv : bv 5) Rb; rewrite Rb; reflexivity|].
    prreg HS (27%bv : bv 5) Rb. rewrite Rb, E25. unfold w64, g1_row.
    f_equal; lia.
Qed.

Lemma g1_main : ge_from B MT (ge_post B MT) (GIS_gbhd B MT) ->
  ge_from B MT (ge_post B MT) (GIS_ga1 B MT).
Proof.
  intros NEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrm Hmo HGI.
  exact (g1_outer (ge_post B MT) _ NEXT cx fp k acc ly3 S3 W3 ms3 md3 eq_refl HB HJ Hfrm Hmo HGI).
Qed.

End d.

(* 0x81104 -> 0x811f8: the second group-A loop of the sweep phase. *)
Lemma gsw_seg_ga1 : SEG_ga1 B MT.
Proof. intros RT NEXT. exact (g1_main RT NEXT). Qed.

End c.
End b.
End a.
