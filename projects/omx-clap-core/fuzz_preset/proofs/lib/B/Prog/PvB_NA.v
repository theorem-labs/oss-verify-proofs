(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B (asan-ubsan), parse_value 0x8637c, SEGMENT N (the number arm), sub-piece A
   of lib/B/Prog/PvB_NCut.v: pnA (pnA_stmt), N 0x86598 -> T 0x8688c | L 0x86718
   (composed into PvB_Top.v's SEG_N).
   rule 24: no function proved
   rule 24: proves no function (kind: segment lemma). Reuse search (04:10Z, `proof-index
   parse_value`, index built 2026-10-29T04:26:29Z): "parse_value: 14 file(s) named for it, 35 file(s) use its address,
   0 related; in the delivery 58 named for it and 794 name(s) that hold it, in 68 tree(s)"; second-agent CONFIRM
   (04:21Z): no released srealizes-form proof of this program's parse_value.
   CODE WALKED (neutral listing, the internal file parse_value.fuzz_preset.asan-ubsan.s): B 0x86598 .. 0x86618 and
   0x866f0 .. 0x86714, 43 instructions: the fake frame's shadow byte 4 cleared (0x8659c), the sign ('-' moves s6 to
   p1 + 1 after the UBSan overflow check 0x865ac), s5 := -1, the end test, the shadow check of x[j0] (slow arm
   0x868b8), the first-digit test,
   the leading-zero test (UBSan check 0x865e8, the end test, the shadow check of x[j0 + 1], slow arm 0x868f4), and at
   0x866f0 the scan registers and the &end spill `sd t0, 24(s1)`. The two slow arms are absorbed by the engine from
   the text's shadow facts; the UBSan checks to 0x86898 are decided from the cursor's range.
   HOW: the PA-listing engine (YC80x / YC1fPx paj_run_to_x over YCbqG's ajournal_x) at the cut's float state fx0, in
   two runs, as image A's S8aNumA.v does (read as a pattern; nothing of image A is Required): run 1 (0x86598 ..
   0x865a0, the shadow byte store, with an empty token band since that byte lies in the shadow band) and run 2
   (0x865a0 onward, the shadow band as the token band, the text bytes x[j0], x[j0 + 1] as a read-only region). The
   case split is up front on c = '-' and on the bytes after j0 (none, one, two or more): 15 leaves.
   THE MEMORY at T / L: the arm writes only [Y + 24, Y + 32) (the real frame) and SHADOW_OFF + fa / 8 + 4 (the fake
   frame's shadow byte 4); pv_body (now with pv_shadow_open) and pv_reader0 (with its room rd_room Sc (pe_gt en), a
   fact of the allocator state only) move from the cut's memory because every byte they read is apart from both: the
   cursor q is above the entry sp, the text and the node lie in allocator blocks, image globals, older fake frames or
   the caller's window, so never in the new fake frame (alx_sep, alx_client_img, alx_layout), and the statics are
   image bytes. The cut's call chain pv_chain is not carried: neither L nor T states it.
   MEMNORM: pv_at_N's last conjunct `YStrtodRowX.aj_memnorm SEGS mem` (the memory normal form, a state fact of the
   cut) goes to L's / T's last conjunct. Every run is lib/Reusable/YSRrMemnorm.v's runner twin paj_run_to_x_inv at
   P := YAkMemnorm.memnorm SEGS (its laws srr_inv_laws_memnorm_k; YStrtodRowX.aj_memnorm is the same body, by
   conversion), driven by the tactic twin paj_run_to_tok_x_inv: the run's start memory's P goes in as HPM, the end
   memory's P comes back as HPM. A branch (paj_branch) keeps the machine state, so HPM stays.
   ROOM: T's outcome (a) (no allocation, no event) carries pv_reader0's rp_keep from the entry (PvB_Room.v), from which
   PvB_NQ.v's pnQ gives pv_Qm's rp_post (rp_nil); L carries it the same way. The ledger's statics include #102's g_most
   and g_own_ran_out (the kit's prh_glob), image bytes the arm does not write (pna_val_static).
   Section hypotheses: LAWS (AR_laws_x at its head length hl, implicit) only; no image fact (the arm reads no image
   word).
   Numerals (brief rule 4): no ADDRESS. DERIVED: the listing offsets 20172 (0x86598), 20180 (0x865a0), 20556
   (0x86718), 20928 (0x8688c) = B pc - B_prog_base 0x816cc; 0x7fff7f800000 / 0x7fffff800000 (alloc_ceiling's bounds,
   YCbq.v asan_consts); 0x7fff8000, 0x7fff7000, 0x10007fff8000, 0x800000000000 (YG0f.v's SHADOW_OFF, kLowMemEnd,
   kLowShadowBeg, kHighShadowEnd / kHighMemBeg, kHighMemEnd, restated by reflexivity for lia); 0x601000
   (YImgTop.IMG_TOP_B, a bound on the alloc.c statics). LENGTH: 24, 32 (the &end slot of the realigned frame), 4, 5, 8,
   40, 64 (the class-0 fake frame and its shadow bytes), 104, 160, 176 (the real frame), 2 ^ 44, 2 ^ 47, 2 ^ 47 - 64,
   2 ^ 64, 4096, 256 (address and byte bounds), 0, 1, 2 (byte counts). WORD: 45 '-', 48 '0', 58, 10,
   18446744073709551606 (-10), -48, -58, 18446744073709551615 (-1) (the listing's immediates as the engine prints
   them), 288230376218820621 (PN_MASK), 255 (a byte); register and atom numbers (2 .. 33). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqG YC80x YC1fPx YG0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YStrtodRowX.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CallerJ.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PvB_Defs PvB_NCut.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PvB_Model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Instance PIBa : PrhImg := prh_img_B.

(* ======== pure: the arm's tests on the first bytes and pn_lead ======== *)

Lemma pna_bytes_all : forall (f : Z -> bool), forallb (fun n => f (Z.of_nat n)) (seq 0 256) = true ->
  forall b, 0 <= b < 256 -> f b = true.
Proof.
intros f H b Hb. rewrite forallb_forall in H.
specialize (H (Z.to_nat b) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia. exact H.
Qed.

(* 0x865d0 `addi a3, a1, -58; li a4, -10; bltu a3, a4`: taken iff the byte is not a digit *)
Lemma pna_digit_lt : forall b, 0 <= b < 256 ->
  (zcanon (b + -58) <? zcanon 18446744073709551606) = negb (PjGrammar.digit b).
Proof.
intros b Hb. apply Bool.eqb_prop.
apply (pna_bytes_all (fun b => Bool.eqb (zcanon (b + -58) <? zcanon 18446744073709551606) (negb (PjGrammar.digit b))));
  [vm_compute; reflexivity | exact Hb].
Qed.

(* 0x86608 `addi a1, a1, -48; li a3, 10; bgeu a1, a3`: not taken iff the byte is a digit *)
Lemma pna_digit_ge : forall b, 0 <= b < 256 -> (zcanon (b + -48) <? zcanon 10) = PjGrammar.digit b.
Proof.
intros b Hb. apply Bool.eqb_prop.
apply (pna_bytes_all (fun b => Bool.eqb (zcanon (b + -48) <? zcanon 10) (PjGrammar.digit b)));
  [vm_compute; reflexivity | exact Hb].
Qed.

(* 0x865e0 `li a3, 48; bne a1, a3` *)
Lemma pna_eq48 : forall b, 0 <= b < 256 -> (zcanon (b + 0) =? zcanon 48) = (b =? 48).
Proof. intros b Hb. rewrite Z.add_0_r, !zcanon_id by (unfold M64; lia). reflexivity. Qed.

Lemma pna_lead_T1 : forall x j0, (length x <= j0)%nat -> ~ pn_lead x j0.
Proof. intros x j0 H (H1 & _). lia. Qed.
Lemma pna_lead_T2 : forall x j0, PjGrammar.digit (nth j0 x 0) = false -> ~ pn_lead x j0.
Proof. intros x j0 H (_ & H2 & _). congruence. Qed.
Lemma pna_lead_T3 : forall x j0, nth j0 x 0 = 48 -> (S j0 < length x)%nat ->
  PjGrammar.digit (nth (S j0) x 0) = true -> ~ pn_lead x j0.
Proof. intros x j0 H1 H2 H3 (_ & _ & H4). exact (H4 (conj H1 (conj H2 H3))). Qed.
Lemma pna_lead_L : forall x j0, (j0 < length x)%nat -> PjGrammar.digit (nth j0 x 0) = true ->
  (nth j0 x 0 <> 48 \/ (length x <= S j0)%nat \/ PjGrammar.digit (nth (S j0) x 0) = false) -> pn_lead x j0.
Proof.
intros x j0 H1 H2 H3. split; [exact H1|]. split; [exact H2|]. intros (H4 & H5 & H6).
destruct H3 as [H3 | [H3 | H3]]; [exact (H3 H4) | lia | congruence].
Qed.

(* the shadow byte SHADOW_OFF + f / 8 + 4 of a 32-aligned frame f covers [f + 32, f + 40) only *)
Lemma pna_div8 : forall z f, f mod 32 = 0 -> z / 8 = f / 8 + 4 -> f + 32 <= z < f + 40.
Proof.
intros z f Hf H.
pose proof (Z.div_mod z 8 ltac:(lia)) as Hz. pose proof (Z.mod_pos_bound z 8 ltac:(lia)) as Hzr.
pose proof (Z.div_mod f 8 ltac:(lia)) as Hf8.
pose proof (Z.div_mod f 32 ltac:(lia)) as Hf32. rewrite Hf, Z.add_0_r in Hf32.
assert (Hm : f mod 8 = 0).
{ rewrite Hf32. replace (32 * (f / 32)) with ((4 * (f / 32)) * 8) by lia. apply Z.mod_mul. lia. }
rewrite Hm, Z.add_0_r in Hf8. lia.
Qed.

Lemma pna_nth_skipn : forall (l : list Z) k j, nth j (skipn k l) 0 = nth (k + j) l 0.
Proof.
induction l as [|a l IH]; intros k j.
- rewrite skipn_nil. destruct j, k; reflexivity.
- destruct k as [|k]; [reflexivity|]. cbn [skipn Nat.add nth]. apply IH.
Qed.

Lemma pna_garr8_skipn : forall segs m base (l : list Z) k, garr8 segs m base l ->
  garr8 segs m (base + Z.of_nat k) (skipn k l).
Proof.
intros segs m base l k H j Hj. rewrite length_skipn in Hj. rewrite pna_nth_skipn.
destruct (H (k + j)%nat ltac:(lia)) as [H1 H2]. split; [|exact H2].
replace (base + Z.of_nat k + Z.of_nat j) with (base + Z.of_nat (k + j)) by lia. exact H1.
Qed.

Lemma pna_nth_byte : forall segs m p (x : list Z) j, garr8 segs m p x -> 0 <= nth j x 0 < 256.
Proof.
intros segs m p x j H. destruct (Nat.lt_ge_cases j (length x)) as [Hj|Hj].
- exact (proj2 (H j Hj)).
- rewrite nth_overflow by exact Hj. lia.
Qed.

(* ======== generic helpers over the engine's state (image A S8aNumA.v's eva_* forms, image independent) ======== *)

Lemma pna_w64_m1 : Z_to_bv 64 18446744073709551615 = w64 (-1).
Proof. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. Qed.

Lemma pna_inw_cons : forall E r rs z, in_wrange E (r :: rs) z ->
  (base_val E (r_base r) + r_wlo r <= z < base_val E (r_base r) + r_whi r) \/ in_wrange E rs z.
Proof. intros E r rs z (r' & [<-|Hin] & Hr); [left; exact Hr | right; exists r'; auto]. Qed.
Lemma pna_inw_nil : forall E z, ~ in_wrange E [] z.
Proof. intros E z (r & Hin & _). destruct Hin. Qed.

Lemma pna_agree_ewset : forall k E E' n v, (k <= n)%nat -> YP06.env_agree k E E' -> YP06.env_agree k E (ewset E' n v).
Proof.
intros k E E' n v Hk [H1 H2]. split.
- intros i Hi. cbn [ew ewset]. destruct (Nat.eqb_spec i n); [lia|]. apply H1. exact Hi.
- cbn [ed ewset]. exact H2.
Qed.

(* the text byte x[j] as a one-byte chunk of atom n *)
Lemma pna_byte_chunk : forall segs E m base off n j (x : list Z) x0,
  garr8 segs m x0 x -> (j < length x)%nat -> base + off = x0 + Z.of_nat j ->
  bv_unsigned (ew E n) = nth j x 0 -> YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal 1 (SOff n 0))).
Proof.
intros segs E m base off n j x x0 Hg Hj Hb Hn i Hi. cbn [YP09.c_len YP09.c_val cv_len YP09.c_off] in *.
assert (i = 0) by lia. subst i. exists (Z_to_bv 8 (nth j x 0)). split.
- cbn [cbyte]. f_equal. unfold byte_of_word. cbn [sv_denot]. rewrite Hn, Z.add_0_r.
  pose proof (proj2 (Hg j Hj)) as Hr. rewrite unsigned_lit_small by lia. rewrite Z.shiftr_0_r. reflexivity.
- rewrite Z.add_0_r, Hb. exact (garr8_mbyte _ _ _ _ _ Hg Hj).
Qed.

(* an 8-byte chunk of a run's state *)
Lemma pna_chunk8 {fx : YK11.FPState} : forall segs val E ss ms r off e,
  st_ok_pi segs val E ss ms -> In r (ss_mem ss) -> In (YP09.mkChunk off (CVal 8 e)) (r_chunks r) ->
  forall v, sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem segs (ms_mem ms) (base_val E (r_base r) + off) 8 v.
Proof.
intros segs val E ss ms r off e HS Hr Hc v He Hv.
pose proof (st_ok_mem_ok segs E _ ms HS) as (_ & Hrs & _). cbn [abs_ss setpc ss_mem] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs r Hr) as (_ & _ & _ & Hcs).
exact (val_of_chunk_ok segs E _ _ off 8 e v (proj1 (Forall_forall _ _) Hcs _ Hc) He ltac:(exact Hv) ltac:(lia)).
Qed.

(* a one-byte zero chunk of a run's state (the shadow byte store at 0x8659c) *)
Lemma pna_chunk1z {fx : YK11.FPState} : forall segs val E ss ms r off,
  st_ok_pi segs val E ss ms -> In r (ss_mem ss) -> In (YP09.mkChunk off (CVal 1 (SLit 0))) (r_chunks r) ->
  YP09.mbyte segs (ms_mem ms) (base_val E (r_base r) + off) = Some (Z_to_bv 8 0).
Proof.
intros segs val E ss ms r off HS Hr Hc.
pose proof (st_ok_mem_ok segs E _ ms HS) as (_ & Hrs & _). cbn [abs_ss setpc ss_mem] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs r Hr) as (_ & _ & _ & Hcs).
destruct (proj1 (Forall_forall _ _) Hcs _ Hc 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
cbn [YP09.c_off] in Hb2. rewrite Z.add_0_r in Hb2. rewrite Hb2. cbn [cbyte YP09.c_val] in Hb1.
injection Hb1 as <-. reflexivity.
Qed.

(* dropping regions of a run's state *)
Lemma pna_submem {fx : YK11.FPState} : forall segs val E ss ms rs,
  st_ok_pi segs val E ss ms -> submem rs (ss_mem ss) -> regions_wf rs = true ->
  st_ok_pi segs val E (mkSS (ss_pc ss) (ss_regs ss) rs (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros segs val E ss ms rs HS Hsub Hwf. unfold st_ok_pi, abs_ss in *.
exact (st_ok_submem segs E (setpc ss (val A_TEXT + ss_pc ss)) ms rs HS Hsub Hwf).
Qed.

Lemma pna_u64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof. intros z Hz. unfold w64. apply unsigned_lit_small. exact Hz. Qed.

(* ======== the symbolic states ======== *)

Definition PNA_Bx : sv := SOff 23 0.
Definition PNA_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* run 1 checks no shadow byte; its band is empty so the fake frame's shadow byte may be written *)
Definition PNA_Bspan0 : Z * Z := (0, 0).
Definition PNA_CEIL : Z := 0x7fff7f800000.
(* Y + 24 .. Y + 32: the &end spill (0x86714) *)
Definition pna_RY : YP09.region := YP09.mkRegion (Some 9%nat) 24 32 24 32 [].
(* the fake frame's shadow byte 4 (0x8659c) *)
Definition pna_RS : YP09.region := YP09.mkRegion (Some 27%nat) 4 5 4 5 [].
(* the text bytes x[j0] (atom 32) and x[j0 + 1] (atom 33), read-only, at a0 = p1 plus sg *)
Definition pna_RT (sg n : Z) : YP09.region :=
  YP09.mkRegion (Some 10%nat) sg (sg + n) 0 0
    (if n =? 1 then [YP09.mkChunk sg (CVal 1 (SOff 32 0))]
     else [YP09.mkChunk sg (CVal 1 (SOff 32 0)); YP09.mkChunk (sg + 1) (CVal 1 (SOff 33 0))]).
Definition pna_atoms : list (nat * afact) :=
  [(9%nat, mkAF PNA_CEIL (2 ^ 47) 5); (10%nat, mkAF 4096 (2 ^ 47 - 64) 0); (12%nat, mkAF 4096 (2 ^ 47 - 64) 0);
   (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (26%nat, mkAF 4096 (2 ^ 47) 5);
   (27%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0); (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0)].
Definition pna_cEQ : acond := mkAC BC_EQ (SOff 11 0) (SLit 45).
Definition pna_cNE : acond := mkAC BC_NE (SOff 11 0) (SLit 45).
Definition pna_cLT (o : Z) : acond := mkAC BC_LTU (SOff 10 o) (SOff 12 0).
Definition pna_cGE (o : Z) : acond := mkAC BC_GEU (SOff 10 o) (SOff 12 0).
Definition pna_ss1 (cs : list acond) : sstate := mkSS 20172 sr_atoms [pna_RY; pna_RS] None (mkFacts pna_atoms cs []).
(* the registers every leaf keeps from the cut *)
Definition pna_kregs : list Prelude.reg :=
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 10%bv; 12%bv; 18%bv; 19%bv; 20%bv; 23%bv; 24%bv; 26%bv; 27%bv].

Section c. Context {fx0 : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Let RUNTO := @paj_run_to_x_inv fx0 rc SK B_prog_listing PL_prog_B PA B (@prh_pst prh_img_B) ARx hl LAWS
  (YAkMemnorm.memnorm SEGS) (srr_inv_laws_memnorm_k SEGS).
Let BR := paj_branch (PI := PA).

Section ctx.
Variable en : PvEnt.
Hypothesis HPRE : pv_pre B ARx en.
Variables (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (Y fa fl pos : Z) (lyc : alayout) (Sc : astate) (k : Z) (c : Z) (y : list Z).
Hypothesis HKR : pv_keep_regs en regs Y fa.
Hypothesis R9 : getr regs 9 = w64 Y.
Hypothesis R19 : getr regs 19 = w64 (pe_v en).
Hypothesis R20 : getr regs 20 = w64 (pe_q en).
Hypothesis R24 : getr regs 24 = w64 (SHADOW_OFF + pe_q en / 8).
Hypothesis HSK : PjGrammar.skip (pe_rest en) = c :: y.
Hypothesis R10 : getr regs 10 = w64 (pe_text en + pe_len en - Z.of_nat (length (c :: y))).
Hypothesis R11 : getr regs 11 = w64 c.
Hypothesis R12 : getr regs 12 = w64 (pe_text en + pe_len en).
Hypothesis HC : c <> 123 /\ c <> 91 /\ c <> 34 /\ c <> 116 /\ c <> 102 /\ c <> 110.
Hypothesis HBODY : pv_body B ARx en Y fa fl pos pv_shadow_live lyc Sc (pe_Hp en) W mem md k.
Hypothesis HRD : pv_reader0 B en pos (pe_text en + pe_len en - Z.of_nat (length (c :: y))) lyc Sc W mem.
(* pv_at_N's last conjunct: the memory normal form at the cut's memory *)
Hypothesis HMN : YStrtodRowX.aj_memnorm SEGS mem.
Local Notation xs := (c :: y).
Local Notation pp1 := (pe_text en + pe_len en - Z.of_nat (length (c :: y))).
Local Notation tnd := (pe_text en + pe_len en).

(* ---- the arithmetic of the cut ---- *)
Lemma pna_F :
  176 <= pe_STK en /\ alloc_ceiling <= pe_sp en - pe_STK en /\ 0 <= pe_e en /\ pe_sp en + pe_e en <= 2 ^ 47 /\
  pe_sp en - 176 <= Y <= pe_sp en - 160 /\ Y mod 32 = 0 /\
  4096 <= fa /\ fa + 64 <= alloc_ceiling /\ fa mod 32 = 0 /\ in_app fa 64 /\
  PNA_CEIL <= alloc_ceiling <= 0x7fffff800000 /\
  4096 <= pe_text en /\ pe_text en + pe_len en <= alloc_ceiling /\ amem_range (pe_text en) (pe_len en) /\
  pe_sp en <= pe_q en /\ pe_q en + 24 <= pe_sp en + pe_e en /\
  Z.of_nat (length xs) <= pe_len en /\ pe_text en <= pp1.
Proof.
pose proof HPRE as (HFPRE & _ & _ & _ & _ & _ & _ & _ & HRDP & _ & _).
pose proof HFPRE as (HAFN & _).
pose proof HAFN as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hc0 & Hlo0 & Hhi0 & H47 & _ & Htop0 & Htop1).
pose proof HRDP as (_ & _ & _ & _ & _ & Hwin & Hqlo & Hqhi & _).
pose proof Hwin as (He0 & _ & Hetop & _).
pose proof HBODY as (HFRM & HinF & Efa & _ & HJ & _).
pose proof HFRM as (HY1 & HY32 & _).
pose proof HJ as (HAR & _).
pose proof HRD as (_ & _ & _ & _ & Hin1 & Hsrc & _).
pose proof Hsrc as (_ & Ht4096 & Htc & Hamr & _).
pose proof Hin1 as (_ & _ & _ & _ & _ & _ & _ & Hpb & Hlen & _).
rewrite Hlen in Htc, Hamr.
destruct (frames_bounds_x SEGS B ARx LAWS lyc Sc (pe_Hp en) W mem md 0 pos HAR HinF) as (Hf0 & Hfc & Hfapp).
destruct (alx_frames SEGS B ARx LAWS lyc Sc (pe_Hp en) W mem md 0 pos HAR HinF) as (Hfal & _).
rewrite <- Efa in Hf0, Hfc, Hfapp, Hfal.
assert (Efb : fs_frame_bytes 0 = 64) by reflexivity. rewrite Efb in Hfc, Hfapp.
pose proof asan_consts as (C1 & _).
assert (HSTK : 176 <= pe_STK en).
{ unfold pe_STK, STK_parse_value.
  match goal with |- 176 <= Z.of_nat (S ?n) * ?F + ?L =>
    assert (HFL : (176 <=? F + L) && (0 <=? F) = true) by (vm_compute; reflexivity);
    apply andb_true_iff in HFL; destruct HFL as [HF1 HF2]; apply Z.leb_le in HF1, HF2;
    assert (1 <= Z.of_nat (S n)) by lia; nia end. }
change (spZ (pe_regs en)) with (pe_sp en) in *.
unfold PNA_CEIL. unfold pe_sp in *.
repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
Qed.

Lemma pna_shb : SHADOW_OFF <= SHADOW_OFF + fa / 8 /\ SHADOW_OFF + fa / 8 + 8 <= kHighShadowEnd /\
  SHADOW_OFF + fa / 8 + 8 <= alloc_ceiling /\ SHADOW_OFF + fa / 8 + 8 <= Y.
Proof.
pose proof pna_F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & _).
unfold PNA_CEIL in F11. unfold kHighShadowEnd, SHADOW_OFF. lia.
Qed.
Ltac pna_Fall :=
  pose proof pna_F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18);
  pose proof pna_shb as (S1 & S2 & S3 & S4); unfold PNA_CEIL in F11;
  assert (KSO : SHADOW_OFF = 0x7fff8000) by reflexivity;
  assert (KHE : kHighShadowEnd = 0x10007fff8000) by reflexivity;
  assert (KHB : kHighMemBeg = 0x10007fff8000) by reflexivity;
  assert (KLE : kLowMemEnd = 0x7fff8000) by reflexivity;
  assert (KLB : kLowShadowBeg = 0x7fff7000) by reflexivity;
  assert (KHM : kHighMemEnd = 0x800000000000) by reflexivity.

(* ---- the bytes the arm does not write ---- *)
Definition pna_NW (a : Z) : Prop := 0 <= a < 2 ^ 64 /\ ~ (Y + 24 <= a < Y + 32) /\ a <> SHADOW_OFF + fa / 8 + 4.
Definition pna_kept (m' : word -> option byte) : Prop :=
  forall a, pna_NW a -> rdW W m' (Z_to_bv 64 a) = rdW W mem (Z_to_bv 64 a).
Definition pna_sh4 (m' : word -> option byte) : Prop :=
  YP09.mbyte SEGS (rdW W m') (SHADOW_OFF + fa / 8 + 4) = Some (Z_to_bv 8 0).
Definition pna_grows (m' : word -> option byte) : Prop := mem_grows (rdW W mem) (rdW W m').

Lemma pna_NW_below : forall a, 0 <= a < Y + 24 -> (a < SHADOW_OFF \/ kHighShadowEnd <= a) -> pna_NW a.
Proof.
intros a Ha Hb. pna_Fall.
split; [lia|]. split; [lia|]. intros ->. lia.
Qed.
Lemma pna_NW_above : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (Y + 24 <= a < Y + 32) -> pna_NW a.
Proof.
intros a Ha Hb. pna_Fall.
split; [unfold PNA_CEIL in F11; lia|]. split; [exact Hb|]. intros ->. lia.
Qed.
Lemma pna_NW_sh : forall z, 0 <= z < 2 ^ 47 -> ~ (fa <= z < fa + 64) -> pna_NW (SHADOW_OFF + z / 8).
Proof.
intros z Hz Hnf. pna_Fall.
unfold pna_NW, SHADOW_OFF in *.
split; [lia|]. split; [lia|]. intros Heq. apply Hnf.
assert (Hq : z / 8 = fa / 8 + 4) by lia. pose proof (pna_div8 z fa F9 Hq). lia.
Qed.
Lemma pna_NW_fsh : forall j, 0 <= j < 8 -> j <> 4 -> pna_NW (SHADOW_OFF + fa / 8 + j).
Proof.
intros j Hj H4. pna_Fall.
split; [unfold kHighShadowEnd in S2; lia|]. split; [lia|]. lia.
Qed.
Lemma pna_NW_fa : forall a, fa <= a < fa + 64 -> pna_NW a.
Proof.
intros a Ha. pna_Fall.
apply pna_NW_below; [lia|].
destruct F10 as (_ & [H1 | (H1 & H2)]); [left | right]; unfold kLowShadowBeg, SHADOW_OFF, kHighMemBeg, kHighShadowEnd in *; lia.
Qed.
Lemma pna_NW_text : forall a, pe_text en <= a < pe_text en + pe_len en -> pna_NW a.
Proof.
intros a Ha. pna_Fall.
apply pna_NW_below; [lia|].
destruct F14 as [H1 | (H1 & H2)]; [left | right]; unfold kLowMemEnd, SHADOW_OFF, kHighMemBeg, kHighShadowEnd in *; lia.
Qed.
Lemma pna_NW_q : forall a, pe_q en <= a < pe_q en + 24 -> pna_NW a.
Proof.
intros a Ha. pna_Fall.
apply pna_NW_above; lia.
Qed.
Lemma pna_NW_v : forall a, pe_v en <= a < pe_v en + 56 -> pna_NW a.
Proof.
intros a Ha. pna_Fall.
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & HRDP & _).
pose proof HRDP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnode & _).
pose proof Hnode as (Hv0 & _ & _ & _ & _ & Hamr & Hown & _).
destruct (Hown a Ha) as (_ & Hnst). change (spZ (pe_regs en)) with (pe_sp en) in Hnst.
destruct (Z_lt_le_dec a alloc_ceiling) as [Hlt | Hge].
- apply pna_NW_below; [lia|].
  destruct Hamr as [H1 | (H1 & H2)]; [left | right]; unfold kLowMemEnd, SHADOW_OFF, kHighMemBeg, kHighShadowEnd in *; lia.
- apply pna_NW_above; [|lia].
  destruct Hamr as [H1 | (H1 & H2)]; unfold kLowMemEnd, kHighMemEnd in *; lia.
Qed.

(* ---- the node and the text are not in the new fake frame ---- *)
Lemma pna_req : forall n, n <= req_size n.
Proof. intros n. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.

Lemma pna_block_nf : forall b m z, In (b, m) (ablocks B lyc Sc) -> b <= z < b + req_size m -> ~ (fa <= z < fa + 64).
Proof.
intros b m z Hin Hz Hf.
pose proof HBODY as (_ & HinF & Efa & _ & HJ & _). pose proof HJ as (HAR & _).
pose proof (sep_block_frame_x SEGS B ARx LAWS lyc Sc (pe_Hp en) W mem md b m 0 pos HAR Hin HinF) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite <- Efa in Hd.
assert (Efb : fs_frame_bytes 0 = 64) by reflexivity. rewrite Efb in Hd. lia.
Qed.

Lemma pna_lam_nf : forall a kk z, In (a, kk) (pe_Lam en) -> a <= z < a + kk -> ~ (fa <= z < fa + 64).
Proof.
intros a kk z Hin Hz.
pose proof HRD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hled & _).
pose proof Hled as (_ & _ & Hblk & _).
rewrite Forall_forall in Hblk. destruct (Hblk _ Hin) as (Hk0 & Hab & _). cbn [fst snd] in *.
pose proof cf_head_nonneg as Hch. pose proof (pna_req (kk + cf_head)).
apply (pna_block_nf _ _ z Hab). lia.
Qed.

Lemma pna_text_nf : forall z, pe_text en <= z < pe_text en + pe_len en -> ~ (fa <= z < fa + 64).
Proof.
intros z Hz.
pose proof HBODY as (_ & HinF & Efa & _ & HJ & _). pose proof HJ as (HAR & _).
pose proof HRD as (_ & _ & _ & _ & _ & _ & Hhome & _).
(* the text's home: a live harness block, a registered read-only global (kept_at's in_zs or kept_img case, both
   in_roP over the text), or a client block *)
destruct Hhome as [[(b & m & Hin & Hb1 & Hb2) | Hk] | (b & m & Hin & _ & Hb1 & Hb2)].
- apply (pna_lam_nf b m z Hin). lia.
- intros Hf. destruct Hk as [(_ & _ & _ & Hro) | (_ & _ & Hro)]; destruct (Hro z Hz) as (Hro1 & _);
    (apply (frm_img_x SEGS B ARx LAWS lyc Sc (pe_Hp en) W mem md 0 pos z HAR HinF);
     [ rewrite <- Efa; assert (Efb : fs_frame_bytes 0 = 64) by reflexivity; rewrite Efb; lia
     | destruct Hro1 as [(s & Hs & _ & Hs1) | Hrl]; [exists s; split; [exact Hs | exact Hs1] | exact (pa_relro_img z Hrl)] ]).
- apply (pna_block_nf b m z Hin). pose proof (pna_req m). lia.
Qed.

Lemma pna_v_nf : forall z, pe_v en <= z < pe_v en + 56 -> ~ (fa <= z < fa + 64).
Proof.
intros z Hz.
pna_Fall.
pose proof HPRE as (HFPRE & _ & _ & _ & _ & _ & _ & _ & HRDP & _).
pose proof HFPRE as ((HAR0 & _) & _).
pose proof HRDP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnode & _).
pose proof Hnode as (_ & _ & _ & _ & Hat & _).
pose proof HBODY as (_ & HinF & Efa & _ & HJ & _). pose proof HJ as (HAR & Hly & _).
pose proof HRD as (Hfr & Hab & _).
destruct Hat as [(a & kk & Hin & Ha1 & Ha2) | [(b & m & Hin & _ & Hb1 & Hb2) | [(cid & p' & Hin & Hp1 & Hp2) | (Hs1 & Hs2)]]].
- apply (pna_lam_nf a kk z Hin). lia.
- rewrite <- Hab in Hin. apply (pna_block_nf b m z Hin). pose proof (pna_req m). lia.
- intros Hf.
  destruct (alx_layout _ _ _ LAWS _ _ _ _ _ _ _ HAR0 Hly) as (_ & Hfa' & _).
  rewrite <- (Hfa' cid p') in Hp1, Hp2.
  destruct (in_split _ _ Hin) as (l2 & l3 & El).
  pose proof (sep_frames_pos_x SEGS B ARx LAWS lyc Sc (pe_Hp en) W mem md (0, pos) (cid, p') [] l2 l3 HAR
    ltac:(rewrite Hfr, El; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite <- Efa in Hd.
  assert (Efb : fs_frame_bytes 0 = 64) by reflexivity. rewrite Efb in Hd.
  pose proof (fs_frame_bytes_nonneg cid). lia.
- change (spZ (pe_regs en)) with (pe_sp en) in Hs1. lia.
Qed.

(* ---- moving the cut's memory facts to a memory that differs only at the two written places ---- *)
Lemma pna_mbyte : forall m', pna_kept m' -> forall a, pna_NW a ->
  YP09.mbyte SEGS (rdW W m') a = YP09.mbyte SEGS (rdW W mem) a.
Proof. intros m' HK a Ha. unfold YP09.mbyte. rewrite (HK a Ha). reflexivity. Qed.
Lemma pna_aview : forall m', pna_kept m' -> forall a, pna_NW a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) mem a.
Proof. intros m' HK a Ha. apply aview_eq_of. exact (HK a Ha). Qed.
Lemma pna_val : forall m', pna_kept m' -> forall a n v, val_mem SEGS (rdW W mem) a n v ->
  (forall i, 0 <= i < Z.of_nat n -> pna_NW (a + i)) -> val_mem SEGS (rdW W m') a n v.
Proof.
intros m' HK a n v H Hn kk Hk. rewrite (pna_mbyte m' HK (a + Z.of_nat kk) (Hn (Z.of_nat kk) ltac:(lia))).
exact (H kk Hk).
Qed.
Lemma pna_garr8 : forall m', pna_kept m' -> forall a l, garr8 SEGS (rdW W mem) a l ->
  (forall i, 0 <= i < Z.of_nat (length l) -> pna_NW (a + i)) -> garr8 SEGS (rdW W m') a l.
Proof.
intros m' HK a l H Hn j Hj. destruct (H j Hj) as [H1 H2]. split; [|exact H2].
apply (pna_val m' HK _ 1 _ H1). intros i Hi.
replace (a + Z.of_nat j + i) with (a + (Z.of_nat j + i)) by lia. apply Hn. lia.
Qed.
Lemma pna_val_static : forall m', pna_kept m' -> forall a n v, val_mem SEGS (rdW W mem) a n v ->
  0 <= a -> a + Z.of_nat n <= 0x601000 -> val_mem SEGS (rdW W m') a n v.
Proof.
intros m' HK a n v H H0 H1. apply (pna_val m' HK _ _ _ H). intros i Hi.
pna_Fall.
apply pna_NW_below; [lia | left; unfold SHADOW_OFF; lia].
Qed.

Lemma pna_kept_refl : pna_kept mem.
Proof. intros a _. reflexivity. Qed.
Lemma pna_grows_refl : pna_grows mem.
Proof. exact (mem_grows_refl _). Qed.
Lemma pna_grows_step : forall m1 m2, pna_grows m1 -> mem_grows (rdW W m1) (rdW W m2) -> pna_grows m2.
Proof. intros m1 m2 H1 H2. exact (mem_grows_trans _ _ _ H1 H2). Qed.
Lemma pna_kept_step : forall E rs m1 m2, pna_kept m1 -> frame_of E rs (rdW W m1) (rdW W m2) ->
  (forall z, 0 <= z < 2 ^ 64 -> in_wrange E rs z -> Y + 24 <= z < Y + 32 \/ z = SHADOW_OFF + fa / 8 + 4) ->
  pna_kept m2.
Proof.
intros E rs m1 m2 HK HF Hw a Ha. rewrite <- (HK a Ha). apply HF.
destruct Ha as (Ha0 & Ha1 & Ha2). rewrite unsigned_lit_small by exact Ha0.
intros Hin. destruct (Hw a Ha0 Hin) as [H|H]; [exact (Ha1 H) | exact (Ha2 H)].
Qed.
Lemma pna_sh4_step : forall E rs m1 m2, pna_sh4 m1 -> frame_of E rs (rdW W m1) (rdW W m2) ->
  ~ in_wrange E rs (SHADOW_OFF + fa / 8 + 4) -> pna_sh4 m2.
Proof.
intros E rs m1 m2 H HF Hn. pna_Fall.
unfold pna_sh4, YP09.mbyte in *. rewrite (HF (Z_to_bv 64 (SHADOW_OFF + fa / 8 + 4))); [exact H|].
rewrite unsigned_lit_small by lia. exact Hn.
Qed.

(* pv_body at the new memory, the fake frame's shadow byte 4 open *)
Lemma pna_body : forall m' md' k',
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (pe_STK en + pe_e en) (pe_sp en + pe_e en) (pe_FP en)
    (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_mem en) (pe_md en) [(0, pos)] lyc Sc (pe_Hp en) W m' md' k' ->
  pna_kept m' -> pna_grows m' -> pna_sh4 m' ->
  pv_body B ARx en Y fa fl pos pv_shadow_open lyc Sc (pe_Hp en) W m' md' k'.
Proof.
intros m' md' k' HJ' HK HG H4.
pna_Fall.
pose proof HBODY as (HFRM & HinF & Efa & Efl & _ & HWIN).
pose proof HFRM as (HY1 & HY32 & HPR0 & Vsav & Vfa48 & Vmagic & Vdesc & Vpc & Vfl & HPRfa & Hshlen & Gsh).

assert (Hsav : Forall (fun oc => -104 <= fst oc <= -8) pv_saved) by (repeat constructor; cbn [fst]; lia).
refine (conj _ (conj HinF (conj Efa (conj Efl (conj HJ' _))))).
- refine (conj HY1 (conj HY32 (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj eq_refl _))))))))))).
  + intros a Ha. exact (apresent_grows (w_H W) mem m' a HG (HPR0 a Ha)).
  + apply Forall_forall. intros oc Hoc. pose proof (proj1 (Forall_forall _ _) Vsav oc Hoc) as Hv.
    pose proof (proj1 (Forall_forall _ _) Hsav oc Hoc) as Hr. cbv beta in Hr, Hv.
    apply (pna_val m' HK _ _ _ Hv). intros i Hi. apply pna_NW_above; cbn in Hi; lia.
  + apply (pna_val m' HK _ _ _ Vfa48). intros i Hi. apply pna_NW_above; cbn in Hi; lia.
  + apply (pna_val m' HK _ _ _ Vmagic). intros i Hi. apply pna_NW_fa. cbn in Hi; lia.
  + apply (pna_val m' HK _ _ _ Vdesc). intros i Hi. apply pna_NW_fa. cbn in Hi; lia.
  + apply (pna_val m' HK _ _ _ Vpc). intros i Hi. apply pna_NW_fa. cbn in Hi; lia.
  + apply (pna_val m' HK _ _ _ Vfl). intros i Hi. apply pna_NW_fa. cbn in Hi; lia.
  + intros a Ha. exact (apresent_grows (w_H W) mem m' a HG (HPRfa a Ha)).
  + intros j Hj. cbn [length pv_shadow_open] in Hj.
    destruct (Nat.eq_dec j 4) as [-> | Hj4].
    * cbn [nth pv_shadow_open]. split; [|lia]. intros kk Hk. assert (kk = 0%nat) by lia. subst kk.
      replace (SHADOW_OFF + fa / 8 + Z.of_nat 4 + Z.of_nat 0) with (SHADOW_OFF + fa / 8 + 4) by lia.
      rewrite H4. reflexivity.
    * destruct (Gsh j ltac:(cbn [length pv_shadow_live]; lia)) as [Hv Hb].
      assert (Ej : nth j pv_shadow_open 0 = nth j pv_shadow_live 0).
      { do 8 (destruct j as [|j]; [first [reflexivity | lia] |]). lia. }
      rewrite Ej. split; [|exact Hb].
      apply (pna_val m' HK _ _ _ Hv). intros i Hi. cbn in Hi.
      replace (SHADOW_OFF + fa / 8 + Z.of_nat j + i) with (SHADOW_OFF + fa / 8 + Z.of_nat j) by lia.
      apply pna_NW_fsh; lia.
- intros a Ha Hnf. rewrite (pna_aview m' HK a ltac:(apply pna_NW_above; lia)). exact (HWIN a Ha Hnf).
Qed.

(* pv_reader0 at the new memory *)
Lemma pna_rd0 : forall m', pna_kept m' -> pna_grows m' -> pv_reader0 B en pos pp1 lyc Sc W m'.
Proof.
intros m' HK HG.
pna_Fall.
pose proof HBODY as (_ & _ & _ & _ & HJ & _). pose proof HJ as (HAR & _).
pose proof HRD as (Hfr & Hab & Hbb & Hroom & Hin & Hsrc & Hhome & Hnode & Hvra & Hled & Hrp).
(* the room (rp_keep from the entry) reads the allocator state Sc only, which the arm does not move *)
refine (conj Hfr (conj Hab (conj Hbb (conj Hroom (conj _ (conj _ (conj Hhome (conj _ (conj _ (conj _ Hrp)))))))))).
- destruct Hin as (Vp & Vend & Vd & Hrw & Hq8 & Ht0 & Ht62 & Hpb & Hlen & Hg & Hqt & Hd).
  refine (conj _ (conj _ (conj _ (conj _ (conj Hq8 (conj Ht0 (conj Ht62 (conj Hpb (conj Hlen (conj _ (conj Hqt Hd))))))))))).
  + apply (pna_val m' HK _ _ _ Vp). intros i Hi. apply pna_NW_q. cbn in Hi; lia.
  + apply (pna_val m' HK _ _ _ Vend). intros i Hi. apply pna_NW_q. cbn in Hi; lia.
  + apply (pna_val m' HK _ _ _ Vd). intros i Hi. apply pna_NW_q. cbn in Hi; lia.
  + intros z Hz. exact (writable_at_grows SEGS _ _ z HG (Hrw z Hz)).
  + apply (pna_garr8 m' HK _ _ Hg). intros i Hi. apply pna_NW_text. lia.
- destruct Hsrc as (Hby & Ht4 & Htc & Hamr & Hra & Hhull).
  refine (conj _ (conj Ht4 (conj Htc (conj Hamr (conj _ _))))).
  + unfold bytes_at in *. apply (pna_garr8 m' HK _ _ Hby). intros i Hi.
    pose proof Hin as (_ & _ & _ & _ & _ & _ & _ & _ & Hlen & _). apply pna_NW_text. lia.
  + intros z Hz. destruct (Hra z Hz) as (s & Hs & Hok). exists s. split; [|exact Hok].
    pose proof Hin as (_ & _ & _ & _ & _ & _ & _ & _ & Hlen & _).
    unfold shadow_of_addr in *. rewrite (pna_aview m' HK); [exact Hs|].
    apply pna_NW_sh; [lia | apply pna_text_nf; lia].
  + intros Hpos s Hs. exact (aview_keeps_vis SEGS (w_H W) mem m' s HG (Hhull Hpos s Hs)).
- intros a Ha. rewrite (pna_aview m' HK a (pna_NW_v a Ha)). exact (Hnode a Ha).
- intros z Hz. destruct (Hvra z Hz) as (s & Hs & Hok). exists s. split; [|exact Hok].
  pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & HRDP & _).
  pose proof HRDP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnode0 & _).
  pose proof Hnode0 as (Hv4096 & _ & _ & _ & _ & Hamr & _).
  unfold shadow_of_addr in *. rewrite (pna_aview m' HK); [exact Hs|].
  apply pna_NW_sh; [| apply pna_v_nf; lia].
  destruct Hamr as [H1 | (H1 & H2)]; unfold kLowMemEnd, kHighMemEnd in *; lia.
- destruct Hled as (Hglob & Hnd & Hblk & Hperm).
  refine (conj _ (conj Hnd (conj _ Hperm))).
  + destruct Hglob as (V1 & V2 & V3 & V4 & V5 & (V6 & R6) & (V7 & R7) & Hrest).
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj (conj _ R6) (conj (conj _ R7) Hrest)))))));
      eapply pna_val_static; first [ eassumption | apply Z.leb_le; vm_compute; reflexivity ].
  + eapply Forall_impl; [|exact Hblk]. intros [a kk] (Hk0 & Hab' & Hhp & Ha16 & Hv). cbn [fst snd] in *.
    refine (conj Hk0 (conj Hab' (conj Hhp (conj Ha16 _)))).
    destruct (alx_blocks SEGS B ARx LAWS lyc Sc (pe_Hp en) W mem md _ _ HAR Hab') as (_ & Hb0 & Hbc & Hbapp & _).
    pose proof cf_head_nonneg as Hch. pose proof (pna_req (kk + cf_head)) as Hrq.
    assert (Hrq1 : 1 <= req_size (kk + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (kk + cf_head) 0); lia).
    apply (pna_val m' HK _ _ _ Hv). intros i Hi. cbn in Hi.
    apply pna_NW_below; [lia|].
    destruct Hbapp as (_ & [H1 | (H1 & H2)]); [left | right];
      unfold kLowShadowBeg, SHADOW_OFF, kHighMemBeg, kHighShadowEnd in *; lia.
Qed.

(* the text x from the cursor p1 *)
Lemma pna_rest : rest_atR (pe_tb en) (pe_text en) pp1 = xs.
Proof.
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & HRDP & _).
pose proof HRDP as (_ & _ & _ & _ & Hcur0 & _).
pose proof Hcur0 as (_ & _ & _ & _ & _ & _ & _ & Hpb & Hlen & _).
destruct (PvB_Model.pvm_skip_rest (pe_tb en) (pe_text en) (pe_len en) (pe_p en) Hlen Hpb) as [H1 _].
unfold pe_rest in HSK. rewrite HSK in H1. exact H1.
Qed.

Lemma pna_x_at : forall m', pv_reader0 B en pos pp1 lyc Sc W m' -> garr8 SEGS (rdW W m') pp1 xs.
Proof.
intros m' (_ & _ & _ & _ & Hin & _).
pose proof Hin as (_ & _ & _ & _ & _ & _ & _ & Hpb & Hlen & Hg & _).
pose proof pna_rest as Hr. unfold rest_atR in Hr.
pose proof (pna_garr8_skipn SEGS _ _ _ (Z.to_nat (pp1 - pe_text en)) Hg) as H.
rewrite Hr, Z2Nat.id in H by lia. replace (pe_text en + (pp1 - pe_text en)) with pp1 in H by lia. exact H.
Qed.

(* ---- the leaves ---- *)
Lemma pna_keep_regs : forall regs', (forall r, In r pna_kregs -> getr regs' r = getr regs r) ->
  pv_keep_regs en regs' Y fa /\ getr regs' 9 = w64 Y /\ getr regs' 19 = w64 (pe_v en) /\
  getr regs' 20 = w64 (pe_q en) /\ getr regs' 24 = w64 (SHADOW_OFF + pe_q en / 8) /\
  getr regs' 10 = w64 pp1 /\ getr regs' 12 = w64 tnd.
Proof.
intros regs' Hkp.
pose proof (Hkp 2%bv ltac:(cbn; tauto)) as K2. pose proof (Hkp 3%bv ltac:(cbn; tauto)) as K3.
pose proof (Hkp 4%bv ltac:(cbn; tauto)) as K4. pose proof (Hkp 8%bv ltac:(cbn; tauto)) as K8.
pose proof (Hkp 9%bv ltac:(cbn; tauto)) as K9. pose proof (Hkp 10%bv ltac:(cbn; tauto)) as K10.
pose proof (Hkp 12%bv ltac:(cbn; tauto)) as K12. pose proof (Hkp 18%bv ltac:(cbn; tauto)) as K18.
pose proof (Hkp 19%bv ltac:(cbn; tauto)) as K19. pose proof (Hkp 20%bv ltac:(cbn; tauto)) as K20.
pose proof (Hkp 23%bv ltac:(cbn; tauto)) as K23. pose proof (Hkp 24%bv ltac:(cbn; tauto)) as K24.
pose proof (Hkp 26%bv ltac:(cbn; tauto)) as K26. pose proof (Hkp 27%bv ltac:(cbn; tauto)) as K27.
destruct HKR as (H2 & H8 & H18 & H26 & H27 & H23 & H3 & H4).
unfold pv_keep_regs.
rewrite K2, K3, K4, K8, K9, K10, K12, K18, K19, K20, K23, K24, K26, K27.
repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

Lemma pna_T : forall regs' m' md',
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (pe_STK en + pe_e en) (pe_sp en + pe_e en) (pe_FP en)
    (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_mem en) (pe_md en) [(0, pos)] lyc Sc (pe_Hp en) W m' md' k ->
  pna_kept m' -> pna_grows m' -> pna_sh4 m' -> YAkMemnorm.memnorm SEGS m' ->
  (forall r, In r pna_kregs -> getr regs' r = getr regs r) -> getr regs' 21 = w64 (-1) ->
  ~ pn_lead xs (pn_sg c) ->
  pn_at_T B ARx en W (@YK11.mkst fx0 regs' (Z_to_bv 64 (BASE + 20928)) m' (YK11.seg_rom SEGS)) md'.
Proof.
intros regs' m' md' HJ' HK HG H4 HPm Hkp H21 Hnl.
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & HRDP & _). pose proof HRDP as (Hfz & _).
destruct (pna_keep_regs regs' Hkp) as (Hkr & _).
destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
exists fx0, regs', m', Y, fa, fl, pos, lyc, Sc, (pe_Hp en), k, (-1).
split; [reflexivity|]. split; [exact Hfz|]. split; [intros r _; reflexivity|].
split; [exact Hkr|]. split; [exact H21|].
split; [exact (pna_body m' md' k HJ' HK HG H4)|].
(* T's run position is outcome (a)'s: the entry's, inside pv_reader0 (the arm makes no allocator step) *)
split; [|exact HPm].
exists c, y. cbv zeta.
refine (conj HSK (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 _))))))).
left. split; [reflexivity|]. split; [exact Hnl|]. split; [reflexivity|]. exact (pna_rd0 m' HK HG).
Qed.

Lemma pna_L : forall (sg : Z) regs' m' md',
  Z.of_nat (pn_sg c) = sg ->
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (pe_STK en + pe_e en) (pe_sp en + pe_e en) (pe_FP en)
    (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_mem en) (pe_md en) [(0, pos)] lyc Sc (pe_Hp en) W m' md' k ->
  pna_kept m' -> pna_grows m' -> pna_sh4 m' -> YAkMemnorm.memnorm SEGS m' ->
  (forall r, In r pna_kregs -> getr regs' r = getr regs r) -> getr regs' 21 = w64 (-1) ->
  getr regs' 13 = w64 10 -> getr regs' 14 = w64 58 -> getr regs' 15 = w64 PN_MASK ->
  getr regs' 22 = w64 (pp1 + sg) -> getr regs' 11 = w64 (pp1 + sg) ->
  val_mem SEGS (rdW W m') (Y + 24) 8 (fa + 32) ->
  pn_lead xs (pn_sg c) ->
  pn_at_L B ARx en W (@YK11.mkst fx0 regs' (Z_to_bv 64 (BASE + 20556)) m' (YK11.seg_rom SEGS)) md'.
Proof.
intros sg regs' m' md' Hsg HJ' HK HG H4 HPm Hkp H21 H13 H14 H15 H22 H11 Hv24 Hlead.
destruct (pna_keep_regs regs' Hkp) as (Hkr & K9 & K19 & K20 & K24 & K10 & K12).
destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
pose proof Hlead as (Hj0 & _).
exists regs', m', Y, fa, fl, pos, lyc, Sc, k, c, y, (pn_sg c). cbv zeta.
unfold pn_p1. rewrite <- Hsg in H22, H11.
split; [reflexivity|].
split; [refine (conj Hkr (conj K9 (conj K19 (conj K20 (conj K24 (conj HSK (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 C6)))))))))))|].
split; [exact (pna_body m' md' k HJ' HK HG H4)|].
split; [exact (pna_rd0 m' HK HG)|].
split; [exact Hv24|]. split; [exact H21|]. split; [exact K10|]. split; [exact K12|].
split; [exact H13|]. split; [exact H14|]. split; [exact H15|]. split; [exact Hlead|].
split; [lia|].
split; [unfold pn_span; rewrite Nat.sub_diag; constructor|].
split; [exact H22 | split; [exact H11 | exact HPm]].
Qed.

Section env.
Variables (b0 b1 : Z) (E0 : env).
Hypothesis Hb0 : b0 = nth (pn_sg c) xs 0.
Hypothesis Hb1 : b1 = nth (S (pn_sg c)) xs 0.
Hypothesis HB0 : 0 <= b0 < 256.
Hypothesis HB1 : 0 <= b1 < 256.
Hypothesis HEI : img_env VAL A_LIM E0.
Hypothesis HAG0 : YP06.env_agree 32 (Ereg regs []) E0.
Hypothesis HRE : regs_ok E0 sr_atoms regs.
Hypothesis U9 : bv_unsigned (ew E0 9) = Y.
Hypothesis U10 : bv_unsigned (ew E0 10) = pp1.
Hypothesis U11 : bv_unsigned (ew E0 11) = c.
Hypothesis U12 : bv_unsigned (ew E0 12) = tnd.
Hypothesis U23 : bv_unsigned (ew E0 23) = SHADOW_OFF.
Hypothesis U26 : bv_unsigned (ew E0 26) = fa.
Hypothesis U27 : bv_unsigned (ew E0 27) = SHADOW_OFF + fa / 8.
Hypothesis U32 : bv_unsigned (ew E0 32) = b0.
Hypothesis U33 : bv_unsigned (ew E0 33) = b1.

Lemma pna_cLT_ok : forall o, 0 <= o <= 2 -> o < Z.of_nat (length xs) -> acond_ok E0 (pna_cLT o).
Proof.
intros o Ho Hl. pna_Fall.

unfold acond_ok, pna_cLT. cbn [ac_c ac_a ac_b]. rewrite branch_ltu_U, !U_SOff, U10, U12.
rewrite !zcanon_id by (unfold M64; lia). apply Z.ltb_lt. lia.
Qed.
Lemma pna_cGE_ok : forall o, 0 <= o <= 2 -> Z.of_nat (length xs) <= o -> acond_ok E0 (pna_cGE o).
Proof.
intros o Ho Hl. pna_Fall.

unfold acond_ok, pna_cGE. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U, !U_SOff, U10, U12.
rewrite !zcanon_id by (unfold M64; lia). apply negb_true_iff, Z.ltb_ge. lia.
Qed.
Lemma pna_cEQ_ok : c = 45 -> acond_ok E0 pna_cEQ.
Proof.
intros H. unfold acond_ok, pna_cEQ. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, U_SOff, U_SLit, U11, H.
vm_compute. reflexivity.
Qed.
Lemma pna_cNE_ok : c <> 45 -> 0 <= c < 256 -> acond_ok E0 pna_cNE.
Proof.
intros H Hc. unfold acond_ok, pna_cNE. cbn [ac_c ac_a ac_b]. rewrite branch_ne_U, U_SOff, U_SLit, U11.
rewrite Z.add_0_r, !zcanon_id by (unfold M64; lia). apply negb_true_iff, Z.eqb_neq. exact H.
Qed.

Lemma pna_entry : forall cs, conds_ok E0 cs ->
  st_ok_pi SEGS VAL E0 (pna_ss1 cs) (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 20172)) mem (seg_rom SEGS))).
Proof.
intros cs Hcs.
pna_Fall.

pose proof HBODY as (HFRM & HinF & Efa & _ & HJ & _). pose proof HJ as (HAR & _).
pose proof HFRM as (_ & _ & HPR0 & _).
destruct (alx_frames SEGS B ARx LAWS lyc Sc (pe_Hp en) W mem md 0 pos HAR HinF) as (_ & _ & _ & Hfsh).
rewrite <- Efa in Hfsh. assert (Efb : fs_frame_bytes 0 / 8 = 8) by reflexivity. rewrite Efb in Hfsh.
rewrite restrict_mkst_fx. unfold pna_ss1. apply pa_entry_st_ok_full.
- exact HRE.
- vm_compute. reflexivity.
- unfold pna_RY, pna_RS. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?U9, ?U27;
    (split; [unfold kHighShadowEnd in *; lia|]); (split; [unfold kHighShadowEnd in *; lia|]); (split; [|constructor]);
    intros o Ho; apply apresent_writable.
  + apply HPR0. lia.
  + replace (SHADOW_OFF + fa / 8 + o) with (shadow_addr fa + 4) by (unfold shadow_addr; lia).
    exact (proj1 (Hfsh 4 ltac:(lia))).
- unfold pna_RY, pna_RS.
  cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
  cbn [YP09.base_val YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite ?U9, ?U27. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
- split; [|split].
  + unfold pna_atoms. cbn [YP0m.f_atoms YP0m.atoms_ok]. unfold YP0m.afact_ok. cbn [YP0m.af_lo YP0m.af_hi YP0m.af_al2].
    rewrite U9, U10, U12, U23, U26, U27, U32, U33. unfold PNA_CEIL, SHADOW_OFF in *.
    repeat match goal with |- _ /\ _ => split end;
      first [ exact I | lia | (change (2 ^ 5) with 32; assumption) | (change (2 ^ 0) with 1; apply Z.mod_1_r) ].
  + exact Hcs.
  + cbn [YP0m.f_alias YP0m.alias_ok]. exact I.
Qed.

(* the region of the text bytes, at a memory the arm has run to *)
Lemma pna_RT_ok : forall E M sg n, pna_kept M -> pna_grows M ->
  bv_unsigned (ew E 10) = pp1 -> sg = Z.of_nat (pn_sg c) ->
  bv_unsigned (ew E 32) = b0 -> bv_unsigned (ew E 33) = b1 ->
  (n = 1 \/ n = 2) -> sg + n <= Z.of_nat (length xs) ->
  region_ok SEGS E (mrestrict (w_H W) M) (pna_RT sg n).
Proof.
intros E M sg n HK HG H10 Hsg H32 H33 Hn Hl.
pose proof (pna_x_at M (pna_rd0 M HK HG)) as Hg.
pna_Fall.

unfold region_ok, pna_RT. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite H10. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
destruct Hn as [-> | ->]; cbn [Z.eqb].
- constructor; [|constructor].
  apply (pna_byte_chunk SEGS E _ _ sg 32 (pn_sg c) xs pp1 Hg); [lia | lia | congruence].
- constructor; [|constructor; [|constructor]].
  + apply (pna_byte_chunk SEGS E _ _ sg 32 (pn_sg c) xs pp1 Hg); [lia | lia | congruence].
  + apply (pna_byte_chunk SEGS E _ _ (sg + 1) 33 (S (pn_sg c)) xs pp1 Hg); [lia | lia | congruence].
Qed.

Lemma pna_RT_disj : forall E r1 sg n, r_base r1 = Some 9%nat -> r_lo r1 = 24 ->
  bv_unsigned (ew E 9) = Y -> bv_unsigned (ew E 10) = pp1 -> 0 <= sg -> 0 <= n ->
  sg + n <= Z.of_nat (length xs) -> all_disjoint E (pna_RT sg n) [r1].
Proof.
intros E r1 sg n Hb Hlo H9 H10 Hsg Hn Hl.
pna_Fall.
cbn [all_disjoint]. split; [|exact I]. unfold extent_disjoint, pna_RT.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Hb, Hlo. cbn [base_val]. rewrite H9, H10. left. lia.
Qed.

(* the shadow check of a text byte at a0 + o (0x865bc, 0x865f4): the text is addressable at the run's memory *)
Lemma pna_obl : forall E M o, pna_kept M -> pna_grows M ->
  bv_unsigned (ew E 23) = SHADOW_OFF -> bv_unsigned (ew E 10) = pp1 -> 0 <= o -> o + 1 <= Z.of_nat (length xs) ->
  range_addressable (rd_of SEGS (mrestrict (w_H W) M)) (U E (SOff 23 0)) (U E (SOff 10 o)) 1.
Proof.
intros E M o HK HG H23 H10 Ho Hl.
pose proof (pna_rd0 M HK HG) as (_ & _ & _ & _ & Hin & Hsrc & _).
pose proof Hin as (_ & _ & _ & _ & _ & _ & _ & _ & Hlen & _).
pose proof Hsrc as (_ & _ & _ & _ & Hra & _).
pna_Fall.

apply (obl_of_range SEGS (w_H W) M E (SOff 23 0) (U E (SOff 10 o)) 1 (pe_text en) (Z.of_nat (length (pe_tb en))) Hra).
- rewrite U_SOff, H23, Z.add_0_r. apply zcanon_id. unfold M64, SHADOW_OFF. lia.
- rewrite U_SOff, H10, zcanon_id by (unfold M64; lia). lia.
- rewrite U_SOff, H10, zcanon_id by (unfold M64; lia). lia.
Qed.

(* ---- the engine runs. The tactics find the walk's hypotheses by their names / types: the state HS (st_ok_pi),
   the journal (ajournal_x), the shadow facts SHOK (sh_ok), the memory invariants HKM (pna_kept), HGM (mem_grows
   from the cut's memory) and HS4 (pna_sh4, after run 1), the run's frames HF / HFr / HG. ---- *)
Ltac pna_regcbn H :=
  cbn [YP09.base_val YP09.r_base YP09.r_wlo YP09.r_whi] in H; cbn [ew ewset Nat.eqb] in H;
  rewrite ?U9, ?U27, ?U10 in H.
Ltac pna_awr1 :=
  unfold awr_byte;
  first [ exfalso; lia
        | left; lia
        | right; right; right; unfold in_frames; exists 0, pos; split; [left; reflexivity|];
          right; unfold in_zr; cbn [fst snd];
          lazymatch goal with Hfa : fa = frame_addr lyc 0 pos |- _ => rewrite <- Hfa end;
          unfold shadow_addr; change (fs_frame_bytes 0 / 8) with 8; lia ].
Ltac pna_awr :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyc ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc lyc own) end;
  unfold awr_ok; let z := fresh "z" in let Hz := fresh "Hz" in intros z Hz;
  repeat (apply pna_inw_cons in Hz; destruct Hz as [Hz|Hz]; [pna_regcbn Hz; pna_awr1|]);
  exfalso; exact (pna_inw_nil _ _ Hz).
Ltac pna_inw_split Hin tac :=
  lazymatch type of Hin with in_wrange ?E ?rs ?zz =>
    let rs' := eval vm_compute in rs in change (in_wrange E rs' zz) in Hin end;
  repeat (apply pna_inw_cons in Hin; destruct Hin as [Hin|Hin]; [pna_regcbn Hin; tac|]);
  exfalso; exact (pna_inw_nil _ _ Hin).
Ltac pna_wset :=
  let z := fresh "z" in let Hz := fresh "Hz" in let Hin := fresh "Hin" in
  intros z Hz Hin; pna_inw_split Hin ltac:(first [left; lia | right; lia | exfalso; lia]).
Ltac pna_nsh := let Hin := fresh "Hin" in intros Hin; pna_inw_split Hin ltac:(exfalso; lia).
(* after a run: the memory invariants at the run's end memory *)
Ltac pna_keep :=
  lazymatch goal with
  | HKM : pna_kept _, HGM : pna_grows _, HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _),
    HG : mem_grows (mrestrict _ _) (mrestrict _ _) |- _ =>
    let HKM' := fresh "HKM" in let HGM' := fresh "HGM" in
    pose proof (pna_kept_step _ _ _ _ HKM HFr ltac:(pna_wset)) as HKM';
    pose proof (pna_grows_step _ _ HGM HG) as HGM';
    try (lazymatch goal with HS4 : pna_sh4 _ |- _ =>
      let H4' := fresh "HS4" in pose proof (pna_sh4_step _ _ _ _ HS4 HFr ltac:(pna_nsh)) as H4'; clear HS4 end);
    clear HKM HGM HG;
    repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx end
  end.
Ltac pna_obl_tac :=
  unfold PNA_Bx; eapply pna_obl;
  [ eassumption | eassumption | cbn [ew ewset Nat.eqb]; exact U23 | cbn [ew ewset Nat.eqb]; exact U10 | lia | lia ].
Ltac pna_run Bsp stop :=
  lazymatch goal with
  | HS : st_ok_pi _ _ _ _ _, HJ : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _,
    HPM : YAkMemnorm.memnorm _ _ |- _ =>
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM Bsp stop
  end;
  lazymatch goal with
  | |- awr_ok _ _ _ _ _ _ _ _ _ => pna_awr
  | |- range_addressable _ _ _ _ => pna_obl_tac
  | |- SRr _ _ _ _ => pna_keep
  end.
(* the fake frame's shadow byte 4 after run 1, from its one-byte zero chunk *)
Ltac pna_fsh_init :=
  lazymatch goal with HS : st_ok_pi _ _ ?E ?ss (restrict (w_H W) ?ms) |- _ =>
    let rs := eval vm_compute in (ss_mem ss) in
    lazymatch rs with [?r1; ?r4] =>
      let H4 := fresh "Hz4" in
      pose proof (pna_chunk1z SEGS VAL E ss (restrict (w_H W) ms) r4 4 HS
        ltac:(change (ss_mem ss) with rs; cbn [In]; tauto) ltac:(cbn [YP09.r_chunks In]; tauto)) as H4;
      cbn [YP09.base_val YP09.r_base ms_mem restrict] in H4; cbn [ew ewset Nat.eqb] in H4; rewrite U27 in H4;
      assert (HS4 : pna_sh4 (ms_mem ms)) by exact H4; clear H4
    end end.
(* run 2 drops the shadow byte's region (it lies in the token band) and reads the text *)
Ltac pna_drop :=
  lazymatch goal with HS : st_ok_pi ?sgs ?v ?E ?ss ?ms |- _ =>
    let rs := eval vm_compute in (ss_mem ss) in
    lazymatch rs with ?r1 :: _ =>
      let HS' := fresh "HS" in
      pose proof (pna_submem sgs v E ss ms [r1] HS
        (submem_keep _ _ _ _ (subregion_refl _) (submem_nil _)) eq_refl) as HS';
      clear HS; rename HS' into HS end end.
Ltac pna_addRT sg n :=
  lazymatch goal with HS : st_ok_pi ?sgs ?v ?E ?ss ?ms |- _ =>
    let rs := eval vm_compute in (ss_mem ss) in
    lazymatch rs with [?r1] =>
      let HS' := fresh "HS" in
      pose proof (st_ok_pi_add_region E ss ms (pna_RT sg n) HS eq_refl
        ltac:(eapply pna_RT_ok; [eassumption | eassumption | cbn [ew ewset Nat.eqb]; exact U10
                                | lazymatch goal with Hsg : pn_sg c = _ |- _ => rewrite Hsg; reflexivity end
                                | cbn [ew ewset Nat.eqb]; exact U32 | cbn [ew ewset Nat.eqb]; exact U33 | lia | lia])
        ltac:(change (ss_mem ss) with rs; apply pna_RT_disj;
              [reflexivity | reflexivity | cbn [ew ewset Nat.eqb]; exact U9 | cbn [ew ewset Nat.eqb]; exact U10
              | lia | lia | lia]))
        as HS';
      clear HS; rename HS' into HS end end.
(* a branch: the two cases, the engine's condition as a byte fact *)
Ltac pna_hc :=
  match goal with H : branch_taken _ _ _ = _ |- _ =>
    first [rewrite branch_ltu_U in H | rewrite branch_ne_U in H | rewrite branch_geu_U in H];
    rewrite ?U_SOff, ?U_SLit in H; cbn [ew ewset Nat.eqb] in H; rewrite ?U32, ?U33 in H;
    first [ rewrite (pna_digit_lt _ HB0) in H | rewrite (pna_digit_ge _ HB1) in H | rewrite (pna_eq48 _ HB0) in H ];
    repeat lazymatch type of H with
    | negb _ = true => apply negb_true_iff in H
    | negb _ = false => apply negb_false_iff in H
    | Z.eqb _ _ = true => apply Z.eqb_eq in H
    | Z.eqb _ _ = false => apply Z.eqb_neq in H
    end
  end.
Ltac pna_branch :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
    psrr_branch_tok RUNTO BR HS SHOK PNA_Bspan end; pna_hc.
(* the leaves: the machine registers and memory at T / L *)
Ltac pna_reg r R :=
  lazymatch goal with HS : st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) |- _ =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as R;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in R;
    cbn [sv_denot ew ewset Nat.eqb] in R
  end.
Ltac pna_kept_tac :=
  lazymatch goal with HS : st_ok_pi _ _ ?E ?ss (restrict _ ?ms) |- _ =>
    let Hk := fresh "Hkp" in
    pose proof (regs_kept_of_st_ok_pi E ss (restrict (w_H W) ms) regs [] pna_kregs HS
       ltac:(repeat (apply pna_agree_ewset; [lia|]); exact HAG0) ltac:(vm_compute; reflexivity)) as Hk;
    cbn [ms_regs restrict] in Hk; exact Hk end.
Ltac pna_r21 := let R := fresh "R" in pna_reg (21%bv : bv 5) R; rewrite R; exact pna_w64_m1.
Ltac pna_rlit r := let R := fresh "R" in pna_reg r R; rewrite R; reflexivity.
Ltac pna_rj r := let R := fresh "R" in pna_reg r R; rewrite R, U10; reflexivity.
Ltac pna_v24 :=
  lazymatch goal with HS : st_ok_pi _ _ ?E ?ss ?msr |- _ =>
    let rs := eval vm_compute in (ss_mem ss) in
    lazymatch rs with context [YP09.mkRegion (Some 9%nat) ?lo ?hi ?wl ?wh ?cs] =>
      let Hv := fresh "Hv" in
      pose proof (pna_chunk8 SEGS VAL E ss msr (YP09.mkRegion (Some 9%nat) lo hi wl wh cs) 24 (SOff 26 32) HS
        ltac:(change (ss_mem ss) with rs; cbn [In]; tauto) ltac:(cbn [YP09.r_chunks In]; tauto) (fa + 32)
        ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U26; reflexivity) ltac:(lia)) as Hv;
      cbn [YP09.base_val YP09.r_base ms_mem restrict ew ewset Nat.eqb] in Hv; rewrite U9 in Hv; exact Hv
    end end.
Ltac pna_pmkst := lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ => pmkst HS end.
Ltac pna_leaf_T K :=
  pna_pmkst; apply K;
  eapply pna_T; [ eassumption | eassumption | eassumption | eassumption | eassumption | pna_kept_tac | pna_r21 | ].
Ltac pna_leaf_L K sg :=
  pna_pmkst; apply K;
  eapply (pna_L sg); [ lazymatch goal with Hsg : pn_sg c = _ |- _ => rewrite Hsg; reflexivity end
                     | eassumption | eassumption | eassumption | eassumption | eassumption | pna_kept_tac
                     | pna_r21 | pna_rlit (13%bv : bv 5) | pna_rlit (14%bv : bv 5) | pna_rlit (15%bv : bv 5)
                     | pna_rj (22%bv : bv 5) | pna_rj (11%bv : bv 5) | pna_v24 | ].

(* the walk of 0x86598 .. 0x86714 / 0x8688c from the cut N *)
Lemma pna_walk : pnK B ARx en (pn_at_T B ARx en) -> pnK B ARx en (pn_at_L B ARx en) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 20172)) mem (seg_rom SEGS)) md) (pv_FINK (SK := SK) B ARx en).
Proof.
intros KT KL.
pna_Fall.

pose proof HBODY as (_ & _ & Efa & _ & HJ & _).
assert (SHOK : sh_ok SEGS PNA_Bx [] E0 (mrestrict (w_H W) mem)) by constructor.
pose proof pna_kept_refl as HKM.
pose proof pna_grows_refl as HGM.
(* the run's P (YSRrMemnorm.v) at the cut's memory *)
assert (HPM : YAkMemnorm.memnorm SEGS mem) by exact HMN.
assert (HC0 : 0 <= c < 256).
{ pose proof (pna_nth_byte _ _ _ _ 0 (pna_x_at mem HRD)) as H. exact H. }
destruct (Z.eq_dec c 45) as [Hc45 | Hc45].
- assert (Hsg : pn_sg c = 1%nat) by (unfold pn_sg; rewrite (proj2 (Z.eqb_eq c 45) Hc45); reflexivity).
  destruct (Nat.lt_ge_cases 1 (length xs)) as [Hj | Hj].
  + destruct (Nat.lt_ge_cases 2 (length xs)) as [Hj2 | Hj2].
    * pose proof (pna_entry [pna_cEQ; pna_cLT 1; pna_cLT 2]
        (conj (pna_cEQ_ok Hc45) (conj (pna_cLT_ok 1 ltac:(lia) ltac:(lia)) (conj (pna_cLT_ok 2 ltac:(lia) ltac:(lia)) I))))
        as HS.
      pna_run PNA_Bspan0 20180. pna_fsh_init. pna_drop. pna_addRT 1 2.
      pna_run PNA_Bspan 20928. pna_branch.
      -- pna_run PNA_Bspan 20928. pna_leaf_T KT. apply pna_lead_T2. rewrite <- Hb0. assumption.
      -- pna_run PNA_Bspan 20556. pna_branch.
         ++ pna_run PNA_Bspan 20556. pna_leaf_L KL 1.
            apply pna_lead_L; [rewrite Hsg; lia | rewrite <- Hb0; assumption | left; rewrite <- Hb0; assumption].
         ++ pna_run PNA_Bspan 20928. pna_branch.
            ** pna_run PNA_Bspan 20556. pna_leaf_L KL 1.
               apply pna_lead_L; [rewrite Hsg; lia | rewrite <- Hb0; assumption | right; right; rewrite <- Hb1; assumption].
            ** pna_run PNA_Bspan 20928. pna_leaf_T KT.
               apply pna_lead_T3; [rewrite <- Hb0; assumption | rewrite Hsg; lia | rewrite <- Hb1; assumption].
    * pose proof (pna_entry [pna_cEQ; pna_cLT 1; pna_cGE 2]
        (conj (pna_cEQ_ok Hc45) (conj (pna_cLT_ok 1 ltac:(lia) ltac:(lia)) (conj (pna_cGE_ok 2 ltac:(lia) ltac:(lia)) I))))
        as HS.
      pna_run PNA_Bspan0 20180. pna_fsh_init. pna_drop. pna_addRT 1 1.
      pna_run PNA_Bspan 20928. pna_branch.
      -- pna_run PNA_Bspan 20928. pna_leaf_T KT. apply pna_lead_T2. rewrite <- Hb0. assumption.
      -- pna_run PNA_Bspan 20556. pna_branch.
         ++ pna_run PNA_Bspan 20556. pna_leaf_L KL 1.
            apply pna_lead_L; [rewrite Hsg; lia | rewrite <- Hb0; assumption | left; rewrite <- Hb0; assumption].
         ++ pna_run PNA_Bspan 20556. pna_leaf_L KL 1.
            apply pna_lead_L; [rewrite Hsg; lia | rewrite <- Hb0; assumption | right; left; rewrite Hsg; lia].
  + pose proof (pna_entry [pna_cEQ; pna_cGE 1]
      (conj (pna_cEQ_ok Hc45) (conj (pna_cGE_ok 1 ltac:(lia) ltac:(lia)) I))) as HS.
    pna_run PNA_Bspan0 20180. pna_fsh_init. pna_drop.
    pna_run PNA_Bspan 20928. pna_leaf_T KT. apply pna_lead_T1. rewrite Hsg. lia.
- assert (Hsg : pn_sg c = 0%nat) by (unfold pn_sg; rewrite (proj2 (Z.eqb_neq c 45) Hc45); reflexivity).
  destruct (Nat.lt_ge_cases 1 (length xs)) as [Hj2 | Hj2].
  + pose proof (pna_entry [pna_cNE; pna_cLT 0; pna_cLT 1]
      (conj (pna_cNE_ok Hc45 HC0) (conj (pna_cLT_ok 0 ltac:(lia) ltac:(cbn [length]; lia))
        (conj (pna_cLT_ok 1 ltac:(lia) ltac:(lia)) I)))) as HS.
    pna_run PNA_Bspan0 20180. pna_fsh_init. pna_drop. pna_addRT 0 2.
    pna_run PNA_Bspan 20928. pna_branch.
    * pna_run PNA_Bspan 20928. pna_leaf_T KT. apply pna_lead_T2. rewrite <- Hb0. assumption.
    * pna_run PNA_Bspan 20556. pna_branch.
      -- pna_run PNA_Bspan 20556. pna_leaf_L KL 0.
         apply pna_lead_L; [rewrite Hsg; cbn [length]; lia | rewrite <- Hb0; assumption | left; rewrite <- Hb0; assumption].
      -- pna_run PNA_Bspan 20928. pna_branch.
         ++ pna_run PNA_Bspan 20556. pna_leaf_L KL 0.
            apply pna_lead_L; [rewrite Hsg; cbn [length]; lia | rewrite <- Hb0; assumption | right; right; rewrite <- Hb1; assumption].
         ++ pna_run PNA_Bspan 20928. pna_leaf_T KT.
            apply pna_lead_T3; [rewrite <- Hb0; assumption | rewrite Hsg; lia | rewrite <- Hb1; assumption].
  + pose proof (pna_entry [pna_cNE; pna_cLT 0; pna_cGE 1]
      (conj (pna_cNE_ok Hc45 HC0) (conj (pna_cLT_ok 0 ltac:(lia) ltac:(cbn [length]; lia))
        (conj (pna_cGE_ok 1 ltac:(lia) ltac:(lia)) I)))) as HS.
    assert (Hl1 : (1 <= length xs)%nat) by (cbn [length]; lia).
    pna_run PNA_Bspan0 20180. pna_fsh_init. pna_drop. pna_addRT 0 1.
    pna_run PNA_Bspan 20928. pna_branch.
    * pna_run PNA_Bspan 20928. pna_leaf_T KT. apply pna_lead_T2. rewrite <- Hb0. assumption.
    * pna_run PNA_Bspan 20556. pna_branch.
      -- pna_run PNA_Bspan 20556. pna_leaf_L KL 0.
         apply pna_lead_L; [rewrite Hsg; cbn [length]; lia | rewrite <- Hb0; assumption | left; rewrite <- Hb0; assumption].
      -- pna_run PNA_Bspan 20556. pna_leaf_L KL 0.
         apply pna_lead_L; [rewrite Hsg; cbn [length]; lia | rewrite <- Hb0; assumption | right; left; rewrite Hsg; lia].
Qed.

End env.

Lemma pna_E0_reg : forall extra n (r : Prelude.reg) v, Z.of_nat n = bv_unsigned r -> getr regs r = w64 v ->
  0 <= v < 2 ^ 64 -> bv_unsigned (ew (Eimg (Ereg regs extra)) n) = v.
Proof.
intros extra n r v Hn Hr Hv. pose proof (u5_range r) as Hr5.
rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs extra n r Hn), Hr. apply pna_u64. exact Hv.
Qed.
Lemma pna_E0_extra : forall w0 w1, 0 <= w0 < 2 ^ 64 -> 0 <= w1 < 2 ^ 64 ->
  bv_unsigned (ew (Eimg (Ereg regs [w64 w0; w64 w1])) 32) = w0 /\
  bv_unsigned (ew (Eimg (Ereg regs [w64 w0; w64 w1])) 33) = w1.
Proof.
intros w0 w1 H0 H1. rewrite !Eimg_low by (unfold A_TEXT; lia).
pose proof (ew_Ereg_extra regs [w64 w0; w64 w1] 0) as E32. pose proof (ew_Ereg_extra regs [w64 w0; w64 w1] 1) as E33.
cbn [Nat.add nth] in E32, E33. rewrite E32, E33. split; apply pna_u64; assumption.
Qed.

(* the sub-piece from the cut, at the env of the cut's registers and the two text bytes after the sign *)
Lemma pna_core : pnK B ARx en (pn_at_T B ARx en) -> pnK B ARx en (pn_at_L B ARx en) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 20172)) mem (seg_rom SEGS)) md) (pv_FINK (SK := SK) B ARx en).
Proof.
intros KT KL.
pose proof (pna_x_at mem HRD) as Hg.
pna_Fall.

destruct HKR as (H2 & H8 & H18 & H26 & H27 & H23 & H3 & H4).
pose proof (pna_nth_byte _ _ _ _ (pn_sg c) Hg) as HB0.
pose proof (pna_nth_byte _ _ _ _ (S (pn_sg c)) Hg) as HB1.
pose proof (pna_nth_byte _ _ _ _ 0 Hg) as HB. cbn [nth] in HB.
set (b0 := nth (pn_sg c) xs 0) in *. set (b1 := nth (S (pn_sg c)) xs 0) in *.
set (E := Eimg (Ereg regs [w64 b0; w64 b1])).
destruct (pna_E0_extra b0 b1 ltac:(lia) ltac:(lia)) as (U32 & U33).
assert (HAG0 : YP06.env_agree 32 (Ereg regs []) E).
{ split; [|reflexivity]. intros n Hn. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite !ew_Ereg_lt by lia. reflexivity. }
assert (U9 : bv_unsigned (ew E 9) = Y) by (apply (pna_E0_reg _ 9 9%bv); [reflexivity | exact R9 | lia]).
assert (U10 : bv_unsigned (ew E 10) = pp1) by (apply (pna_E0_reg _ 10 10%bv); [reflexivity | exact R10 | lia]).
assert (U11 : bv_unsigned (ew E 11) = c) by (apply (pna_E0_reg _ 11 11%bv); [reflexivity | exact R11 | lia]).
assert (U12 : bv_unsigned (ew E 12) = tnd) by (apply (pna_E0_reg _ 12 12%bv); [reflexivity | exact R12 | lia]).
assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF)
  by (apply (pna_E0_reg _ 23 23%bv); [reflexivity | exact H23 | unfold SHADOW_OFF; lia]).
assert (U26 : bv_unsigned (ew E 26) = fa) by (apply (pna_E0_reg _ 26 26%bv); [reflexivity | exact H26 | lia]).
assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF + fa / 8)
  by (apply (pna_E0_reg _ 27 27%bv); [reflexivity | exact H27 | unfold kHighShadowEnd in S2; lia]).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (HRE : regs_ok E sr_atoms regs) by (unfold E; apply regs_ok_Eimg_Ereg).
eapply (pna_walk b0 b1 E); try eassumption; reflexivity.
Qed.

End ctx.

(* ======== the sub-piece: pnA_stmt (PvB_NCut.v) ======== *)
Theorem pnA : @pnA_stmt fx0 rc ci cp RL SK PA B ARx.
Proof.
intros en HPRE KT KL W ms md HN.
(* the cut's call chain pv_chain (after pv_body) is not needed: L and T do not state it *)
destruct HN as (regs & mem & Y & fa & fl & pos & lyc & Sc & k & c & y & Ems & HKR & R9 & R19 & R20 & R24 & HSK &
  R10 & R11 & R12 & C1 & C2 & C3 & C4 & C5 & C6 & HBODY & _ & HRD & HMN).
subst ms.
eapply pna_core; try eassumption.
repeat split; assumption.
Qed.

End c.
