(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgParseL.v at afaa3cb55c1 (the engine plumbing
   of a segment of a parse walk and its arithmetic lemmas U_subba, U_sext32, U_sext32_eqb, U_next, U_and3, U_off_of,
   U_s8), for reac_headamp_prop_parse_result's pair loop on reac-pw/fuzz_headamp's ASan + UBSan image B, its two
   segments WALK and ADV of lib/AU/HPgParseCut.v; the entry states, exits, the strncmp call inside the frame hole and
   the walks below are new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/AU/HPgParseW.v at f7ae59d74add (pbW_rgood,
   pbW_wr, pbW_awr, pbW_keep, pbW_fixed, pbW_pres, pbW_reg_kept, pbW_reg_U, pbW_temps_val, pbW_stop, pbW_entry,
   pbW_cfg_stop, pbW_U_reg0, pbW_inside_A, pbW_out_B, pbW_ko_none, pbW_keyv_lb and the run tactics pbW_post ..
   pbW_ukept) stated over segs with the prefix hgr_, the entry state's regions after the temporaries left to the
   caller (no saves region forced), the run tactics taking the code table's table_ok lemma; the bound on the keys
   counted (hgr_keys_bound, hgr_walk_keys) and hgr_kept_val are new. *)
(* reac-pw/fuzz_headamp: the IMAGE-INDEPENDENT plumbing of the symbolic runs of the walks of
   reac_headamp_prop_parse_result in both ASan images (image A lib/A/HPgParseWalk.v, image B lib/AU/HPgParseW.v):
   the entry state at a cut (the temporaries region at sp = spa with the frame cells a segment reads, and the
   segment's own regions), the write set of a run (the temporaries only), hp_core at a stop of such a run, the values
   a stop holds in registers and in the temporaries, the model at the pair loop's tests, and the tactics that chain
   the runs. No image numeral: every lemma is over segs with the one Section hypothesis segs_low. Proves no function
   (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Accessors Spa Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import FMupoison.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgHole HPgParseBase HPgParseGKit.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgParseGWalk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================= outside any image ======================================= *)
(* the regions of every run: read-only ones, and the temporaries at sp = spa (atom 2) writable inside [spa, spa + 0x80) *)
Definition hgr_rgood (r : YP09.region) : bool :=
(YP09.r_whi r <=? YP09.r_wlo r) ||
(obase_eqb (YP09.r_base r) (Some 2%nat) && (0 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 0x80)).

Lemma hgr_wr : forall E rs a spa, bv_unsigned (ew E 2) = spa -> forallb hgr_rgood rs = true ->
in_wrange E rs a -> spa <= a < spa + 0x80.
Proof.
intros E rs a spa H2 Hg (rg & Hin & Ha). pose proof (proj1 (forallb_forall _ _) Hg rg Hin) as Hr.
unfold hgr_rgood in Hr. apply orb_prop in Hr as [Hr|Hr]; [apply Z.leb_le in Hr; lia|].
apply andb_prop in Hr as [Hr Hhi]. apply andb_prop in Hr as [Hb Hlo]. apply Z.leb_le in Hhi, Hlo.
destruct (YP09.r_base rg) as [b|] eqn:Eb; [|discriminate Hb]. cbn in Hb. apply Nat.eqb_eq in Hb. subst b.
cbn [base_val] in Ha. lia.
Qed.

(* the registers every cut keeps, as the symbolic state holds them *)
Definition hgr_fixed (sr : list sv) : Prop :=
sr_get sr 2%bv = SOff 2 0 /\ sr_get sr 3%bv = SOff 3 0 /\ sr_get sr 4%bv = SOff 4 0 /\ sr_get sr 8%bv = SOff 8 0 /\
sr_get sr 9%bv = SOff 9 0 /\ sr_get sr 18%bv = SOff 18 0 /\ sr_get sr 19%bv = SOff 19 0 /\
sr_get sr 26%bv = SOff 26 0 /\ sr_get sr 27%bv = SOff 27 0.

(* a callee-saved register across a call *)
Lemma hgr_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. pose proof (HP (bv_unsigned r) Hr) as H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.

(* the keys a fold state counts are at most the pod's bytes, when the fold ends in the model's answer *)
Lemma hgr_keys_bound : forall bs cap ps cl keys rf,
Headamp.parse_model bs cap = Headamp.ha_result (Headamp.ha_fold Headamp.parse_cell cap ps cl keys rf) ->
keys <= Z.of_nat (length bs).
Proof.
intros bs cap ps cl keys rf H. pose proof (Headamp.parse_model_keys bs cap) as K. rewrite H in K.
pose proof (Headamp.ha_fold_keys Headamp.parse_cell cap ps cl keys rf) as F.
destruct (Headamp.ha_fold Headamp.parse_cell cap ps cl keys rf) as [[c k] f].
unfold Headamp.ha_result in K. cbv beta iota zeta in K. cbn [fst snd] in F. lia.
Qed.

(* ======================================= over segs ======================================= *)
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {segs : list Segment}.
Variable B : asyms.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Context {akey aph apad asens gotw guard : Z} {dcs : list (Z * Z)}.
Local Notation call_ok := (hp_call_ok B akey aph apad asens gotw guard dcs).
Implicit Types (x : @hp_ctx segs).

(* the write set of a run whose regions are hgr_rgood *)
Lemma hgr_awr : forall x E rs bl0 blc ly own U, call_ok x -> bv_unsigned (ew E 2) = hx_spa x ->
forallb hgr_rgood rs = true -> awr_okH E rs (hx_STK x) (hx_sp0 x) (hx_FP x) bl0 blc ly own U.
Proof.
intros x E rs bl0 blc ly own U Hc H2 Hg a Ha. pose proof (hgr_wr E rs a _ H2 Hg Ha) as Hw.
pose proof (hk_stack B x Hc) as HS. pose proof (hk_frame_win B x Hc) as HW.
left. left. unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *. lia.
Qed.

(* a run's frame keeps every byte outside the temporaries *)
Lemma hgr_keep : forall x E rs (m0 m m' : word -> option byte), bv_unsigned (ew E 2) = hx_spa x ->
forallb hgr_rgood rs = true -> frame_of E rs m m' ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x <= a < hx_spa x + 0x80) -> m (Z_to_bv 64 a) = m0 (Z_to_bv 64 a)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x <= a < hx_spa x + 0x80) -> m' (Z_to_bv 64 a) = m0 (Z_to_bv 64 a)).
Proof.
intros x E rs m0 m m' H2 Hg HF HK a Ha Hn. rewrite (HF (Z_to_bv 64 a)); [exact (HK a Ha Hn)|].
rewrite unsigned_lit_small by exact Ha. intros Hw. exact (Hn (hgr_wr E rs a _ H2 Hg Hw)).
Qed.

(* a register the run left as an atom of the entry env *)
Lemma hgr_reg_kept : forall F fc E0 E ss ms (H : word -> bool) k n (r : bv 5),
st_ok (fx := mkFP F fc) segs E ss (restrict H ms) -> env_agree k E0 E -> (n < k)%nat ->
sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = ew E0 n.
Proof.
intros F fc E0 E ss ms H k n r HS HAE Hn Hsr.
rewrite (st_ok_restrict_reg segs H E ss ms r HS), Hsr, hk_sv_SOff0. exact (proj1 HAE n Hn).
Qed.

(* a register the run left as an atom of the entry env, by its value at the entry (no bound on the value) *)
Lemma hgr_kept_val : forall F fc x regs L E ss ms k (n : nat) (r : bv 5) v,
st_ok (fx := mkFP F fc) segs E ss (restrict (w_H (hx_W x)) ms) -> env_agree k (hk_env x regs L) E -> (n < k)%nat ->
Z.of_nat n = bv_unsigned r -> sr_get (ss_regs ss) r = SOff n 0 -> getr regs r = v -> getr (ms_regs ms) r = v.
Proof.
intros F fc x regs L E ss ms k n r v HS HAE Hk Hn Hsr Hv.
rewrite (hgr_reg_kept F fc _ E ss ms _ k n r HS HAE Hk Hsr), (hk_env_reg x regs L n r Hn). exact Hv.
Qed.

Lemma hgr_reg_U : forall F fc E ss ms (H : word -> bool) (r : bv 5) v,
st_ok (fx := mkFP F fc) segs E ss (restrict H ms) -> U E (sr_get (ss_regs ss) r) = v -> getr (ms_regs ms) r = w64 v.
Proof.
intros F fc E ss ms H r v HS Hv. rewrite (st_ok_restrict_reg segs H E ss ms r HS), denot_lit_U, Hv. reflexivity.
Qed.

(* a frame temporary the run's state holds as a chunk of the temporaries region *)
Lemma hgr_temps_val : forall F fc x E ss ms cs o v w,
st_ok (fx := mkFP F fc) segs E ss (restrict (w_H (hx_W x)) ms) -> In (hk_temps cs) (ss_mem ss) ->
bv_unsigned (ew E 2) = hx_spa x -> In (YP09.mkChunk o (CVal 8 v)) cs -> U E v = w ->
val_mem segs (hx_rd x (ms_mem ms)) (hx_spa x + o) 8 w.
Proof.
intros F fc x E ss ms cs o v w HS Hin H2 Hc Hv.
pose proof (st_ok_mem_ok segs E ss _ HS) as (_ & HR & _).
pose proof (proj1 (Forall_forall _ _) HR _ Hin) as HT. cbn [ms_mem restrict] in HT.
unfold region_ok, hk_temps in HT. cbn [YP09.r_base YP09.r_chunks base_val] in HT. rewrite H2 in HT.
destruct HT as (_ & _ & _ & HC). pose proof (proj1 (Forall_forall _ _) HC _ Hc) as Hck.
pose proof (U_range E v) as R. rewrite Hv in R. unfold M64 in R.
exact (val_of_chunk_ok segs E _ _ o 8 v w Hck ltac:(rewrite denot_lit_U, Hv; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.

(* hp_core at a stop of a run that wrote only the temporaries *)
Lemma hgr_stop : forall F fc x pat cl rb regs mem md L E ss ms md2 k,
api_env segs B -> call_ok x -> hp_core B x pat cl rb regs mem md ->
Z.of_nat (length cl) <= hx_cap x + 1 -> length rb = 12%nat ->
st_ok (fx := mkFP F fc) segs E ss (restrict (w_H (hx_W x)) ms) -> env_agree k (hk_env x regs L) E -> (28 <= k)%nat ->
hgr_fixed (ss_regs ss) ->
ajournal segs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) pat) (ms_mem ms)) md2 (hx_k x) ->
same_io md md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x <= a < hx_spa x + 0x80) ->
 hx_rd x (ms_mem ms) (Z_to_bv 64 a) = hx_rd x mem (Z_to_bv 64 a)) ->
hp_core B x pat cl rb (ms_regs ms) (ms_mem ms) md2.
Proof.
intros F fc x pat cl rb regs mem md L E ss ms md2 k Henv Hc HC Hcl Hrb HS HAE Hk
  (F2 & F3 & F4 & F8 & F9 & F18 & F19 & F26 & F27) HJ Hio KM.
apply (hk_core_frame B segs_low x pat cl rb regs mem md (ms_regs ms) (ms_mem ms) md2 0 0x80 Henv Hc HC Hcl Hrb);
  [lia | lia | intros a Ha Hn; apply KM; [exact Ha | lia] | exact HJ | exact Hio |].
apply (hk_cregs_same x regs (ms_regs ms) (hk_core_cregs B x _ _ _ _ _ _ HC));
[ rewrite (hgr_reg_kept F fc _ E ss ms _ k 2 2%bv HS HAE ltac:(lia) F2); apply hk_env_reg; reflexivity
| rewrite (hgr_reg_kept F fc _ E ss ms _ k 3 3%bv HS HAE ltac:(lia) F3); apply hk_env_reg; reflexivity
| rewrite (hgr_reg_kept F fc _ E ss ms _ k 4 4%bv HS HAE ltac:(lia) F4); apply hk_env_reg; reflexivity
| rewrite (hgr_reg_kept F fc _ E ss ms _ k 8 8%bv HS HAE ltac:(lia) F8); apply hk_env_reg; reflexivity
| rewrite (hgr_reg_kept F fc _ E ss ms _ k 9 9%bv HS HAE ltac:(lia) F9); apply hk_env_reg; reflexivity
| rewrite (hgr_reg_kept F fc _ E ss ms _ k 18 18%bv HS HAE ltac:(lia) F18); apply hk_env_reg; reflexivity
| rewrite (hgr_reg_kept F fc _ E ss ms _ k 19 19%bv HS HAE ltac:(lia) F19); apply hk_env_reg; reflexivity
| rewrite (hgr_reg_kept F fc _ E ss ms _ k 26 26%bv HS HAE ltac:(lia) F26); apply hk_env_reg; reflexivity
| rewrite (hgr_reg_kept F fc _ E ss ms _ k 27 27%bv HS HAE ltac:(lia) F27); apply hk_env_reg; reflexivity ].
Qed.

(* the entry state at a cut: the temporaries with the segment's chunks, then the segment's regions *)
Lemma hgr_entry : forall F fc x pat cl rb regs mem md L pc sr cs rs fs,
call_ok x -> hp_core B x pat cl rb regs mem md ->
regs_ok (hk_env x regs L) sr regs ->
regions_wf (hk_temps cs :: rs) = true ->
Forall (YP09.chunk_ok segs (hk_env x regs L) (hx_rd x mem) (hx_spa x)) cs ->
Forall (region_ok segs (hk_env x regs L) (hx_rd x mem)) rs ->
pairwise_disjoint (hk_env x regs L) (hk_temps cs :: rs) ->
atoms_ok (hk_env x regs L) fs ->
st_ok (fx := mkFP F fc) segs (hk_env x regs L)
  (mkSS pc sr (hk_temps cs :: rs) None (mkFacts (hk_atoms ++ fs) [] []))
  (restrict (w_H (hx_W x)) (mkst (fx := mkFP F fc) regs (Z_to_bv 64 pc) mem (seg_rom segs))).
Proof.
intros F fc x pat cl rb regs mem md L pc sr cs rs fs Hc HC Hsr Hwf Hcs Hrs Hpd Hfs.
rewrite restrict_mkst_fx. unfold hk_env in *. apply (entry_st_ok_full segs); [exact Hsr | exact Hwf | | exact Hpd |].
- apply Forall_cons; [exact (hk_temps_ok B x pat cl rb regs mem md L cs Hc HC Hcs) | exact Hrs].
- split; [|split; exact I]. exact (hk_atoms_ok B x regs L fs Hc (hk_core_cregs B x _ _ _ _ _ _ HC) Hfs).
Qed.

(* a stop as a configuration at its pc *)
Lemma hgr_cfg_stop : forall F fc E ss ms (H : word -> bool) pc md2,
st_ok (fx := mkFP F fc) segs E ss (restrict H ms) -> ss_resv ss = None -> ss_pc ss = pc ->
mkCfg ms md2 = cfg_at (fx := mkFP F fc) segs pc (ms_regs ms) (ms_mem ms) md2.
Proof. intros F fc E ss ms H pc md2 HS Hrv Hpc. rewrite (st_ok_restrict_mkst segs H E ss ms HS Hrv), Hpc. reflexivity. Qed.

(* a register is 0 exactly when its atom is *)
Lemma hgr_U_reg0 : forall x regs L (n : nat) (rg : bv 5), Z.of_nat n = bv_unsigned rg ->
(U (hk_env x regs L) (SOff n 0) = 0 <-> getr regs rg = w64 0).
Proof.
intros x regs L n rg Hn. rewrite U_SOff, (hk_env_reg x regs L n rg Hn). unfold zcanon, M64.
pose proof (bv_unsigned_in_range _ (getr regs rg)) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2 ^ 64) in R.
rewrite Z.add_0_r, Z.mod_small by lia. split; intros H.
- apply bv_eq. rewrite H. reflexivity.
- rewrite H. reflexivity.
Qed.

(* ======================================= the model at the pair loop's tests ======================================= *)
(* the child's header lies in the Struct body: spa_pod_is_inside is the test of the child's size *)
Lemma hgr_inside_A : forall x r cc, r + 16 <= cc -> cc mod 8 = 0 -> cc + 8 <= r + 16 + hp_vs x r ->
Spa.pod_is_inside (hx_bs x) (r + 16) (hp_vs x r) cc = (Spa.u32_at (hx_bs x) cc <=? r + 8 + hp_vs x r - cc).
Proof.
intros x r cc H1 H2 H3. rewrite hgw_inside by lia.
rewrite (proj2 (Z.leb_le (cc - (r + 16)) (hp_vs x r - 8))) by lia. reflexivity.
Qed.

(* it does not *)
Lemma hgr_out_B : forall x r cc, r + 16 <= cc -> cc mod 8 = 0 -> r + 16 + hp_vs x r < cc + 8 ->
Spa.pod_is_inside (hx_bs x) (r + 16) (hp_vs x r) cc = false.
Proof.
intros x r cc H1 H2 H3. destruct (Z_lt_le_dec (hp_vs x r) 8) as [L|L]; [apply hgw_inside_small; exact L|].
rewrite hgw_inside by lia. rewrite (proj2 (Z.leb_gt (cc - (r + 16)) (hp_vs x r - 8))) by lia. reflexivity.
Qed.

(* the key slot after a child that fails one of spa_pod_get_string's first three tests *)
Lemma hgr_ko_none : forall x cc, 0 <= cc ->
(2 ^ 20 <= Spa.u32_at (hx_bs x) cc \/ Spa.u32_at (hx_bs x) cc = 0 \/ Spa.u32_at (hx_bs x) (cc + 4) <> 8) ->
hgw_ko x cc = None.
Proof.
intros x cc H0 H. unfold hgw_ko. rewrite (hgw_gs (hx_bs x) cc H0).
destruct H as [H|[H|H]].
- rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity.
- rewrite H. destruct (0 <? 2 ^ 20), (Spa.u32_at (hx_bs x) (cc + 4) =? 8); reflexivity.
- rewrite (proj2 (Z.eqb_neq _ _) H). rewrite andb_false_r. reflexivity.
Qed.

(* the key register after a String-sized child: the child's text when its last body byte is NUL *)
Lemma hgr_keyv_lb : forall x cc, 0 <= cc ->
1 <= Spa.u32_at (hx_bs x) cc < 2 ^ 20 -> Spa.u32_at (hx_bs x) (cc + 4) = 8 ->
hp_keyv x (hgw_ko x cc) =
if bv_unsigned (nth (Z.to_nat (cc + 8 + Spa.u32_at (hx_bs x) cc - 1)) (hx_bs x) Cursor.NUL) =? 0
then hx_P x + cc + 8 else 0.
Proof.
intros x cc H0 H1 H2. rewrite hgw_keyv_ko, (hgw_gs (hx_bs x) cc H0).
rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite H2, (proj2 (Z.leb_le 1 _)) by lia. cbn [Z.eqb andb].
destruct (_ =? 0); reflexivity.
Qed.

(* the keys counted at the pair loop's head are at most the pod's bytes *)
Lemma hgr_walk_keys : forall x r cc n ko cl keys rf, hp_m_walk x r cc n ko cl keys rf -> keys <= hx_len x.
Proof.
intros x r cc n ko cl keys rf (_ & _ & _ & _ & _ & _ & _ & HW).
exact (hgr_keys_bound (hx_bs x) (hx_cap x) _ cl keys rf HW).
Qed.

End g.

(* ======================================= the run tactics ======================================= *)
(* HAE : env_agree k E0 E (E0 the entry env, E the current one), KM : the bytes outside the temporaries as at the
   entry, Hio : same_io md0 md, U2 : bv_unsigned (ew E0 2) = hx_spa x, Hc : the call's premises; tblok the code
   table's table_ok lemma. *)
Ltac hgr_ne0 := let H0 := fresh "H0" in intros H0; apply (f_equal bv_unsigned) in H0; vm_compute in H0; discriminate H0.
Ltac hgr_post x HAE KM Hio U2 :=
  lazymatch goal with HS : st_ok _ ?E' _ _ |- _ =>
  lazymatch type of HAE with env_agree ?k ?E0 ?E1 =>
  lazymatch goal with HFr : frame_of E1 ?rs (mrestrict _ _) (mrestrict _ _) |- _ =>
    let KM' := fresh "KM" in
    pose proof (hgr_keep x E1 rs _ _ _ ltac:(first [exact U2 | rewrite (proj1 HAE 2%nat ltac:(lia)); exact U2])
      ltac:(vm_compute; reflexivity) HFr KM) as KM';
    clear KM; rename KM' into KM end;
  let H' := fresh "HAE'" in assert (H' : env_agree k E0 E') by env_agree_chain HAE; clear HAE; rename H' into HAE
  end end;
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?md _ |- _ =>
  lazymatch type of Hio with same_io ?m0 _ =>
  let H' := fresh "Hio'" in
  assert (H' : same_io m0 md)
    by (first [exact Hio | eapply same_io_trans; [exact Hio | apply same_io_materialized; apply same_but_materialized_wvb_any]]);
  clear Hio; rename H' into Hio end end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac hgr_awr_tac x Hc HAE U2 :=
  apply (hgr_awr _ x _ _ _ _ _ _ _ Hc);
  [ first [exact U2 | rewrite (proj1 HAE 2%nat ltac:(lia)); exact U2] | vm_compute; reflexivity].
Ltac hgr_run tblok x Hc HAE KM Hio U2 :=
  lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  aj_run_tokH tblok HS HJ SHOK hk_Bspan; [hgr_awr_tac x Hc HAE U2 | ] end;
  hgr_post x HAE KM Hio U2.
Ltac hgr_run_to tblok x Hc HAE KM Hio U2 stop :=
  lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  aj_run_to_tokH tblok HS HJ SHOK hk_Bspan stop; [hgr_awr_tac x Hc HAE U2 | ] end;
  hgr_post x HAE KM Hio U2.
Ltac hgr_branch tblok HAE HB :=
  lazymatch goal with HS : st_ok _ _ _ _, SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok tblok HS SH hk_Bspan end;
  lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into HB end;
  rewrite ?branch_ltu_U, ?branch_geu_U, ?branch_eq_U, ?branch_ne_U in HB;
  lazymatch type of HAE with env_agree ?k ?E0 ?E1 =>
  first [ constr_eq E0 E1 | repeat (rewrite (U_agree k E0 E1 _ HAE) in HB by (vm_compute; reflexivity)) ] end.
(* the goal U E (sr_get (ss_regs ss) r) = _ with the register's form computed and read in the entry env *)
Ltac hgr_ureg HAE :=
  lazymatch goal with |- U ?E (sr_get (ss_regs ?ss) ?r) = _ =>
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
  replace (sr_get (ss_regs ss) r) with e by (vm_compute; reflexivity) end;
  lazymatch type of HAE with env_agree ?k ?E0 ?E1 =>
  first [constr_eq E0 E1 | rewrite (U_agree k E0 E1 _ HAE) by (vm_compute; reflexivity)] end.
Ltac hgr_uat HAE H := first [exact H | rewrite (U_agree _ _ _ _ HAE) by (vm_compute; reflexivity); exact H].
Ltac hgr_ukept HAE H := hgr_ureg HAE; exact H.
Ltac hgr_in := vm_compute; repeat first [left; reflexivity | right].
Ltac hgr_fixed_tac := repeat split; vm_compute; reflexivity.

Print Assumptions hgr_stop.
Print Assumptions hgr_entry.
