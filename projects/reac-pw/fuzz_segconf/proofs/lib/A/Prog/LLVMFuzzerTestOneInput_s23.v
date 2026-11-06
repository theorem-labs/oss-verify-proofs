(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the first half of a round of the split loop of LLVMFuzzerTestOneInput's inlined words_of (plugin-hostd/fuzz_command, 0x86850 .. 0x868a4: the strspn wrapper call, the exit when only separators are left, the 8-byte check and the store of the word's address, the strcspn wrapper call), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACbk.v (a symbolic seed at a point of the function and the runs from it) and A/ACh2.v:122-290 (a call and back, with the facts carried over it); the two wrapper call steps aj_strspn_at_loc and aj_strcspn_at_loc are lib/A/Prog/check_words_art.v's aj_strspn_at and aj_strcspn_at (PaArt.v's aj_art_at), with the guard cells from CmdRecFacts' cmd_rec_cells. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/LLVMFuzzerTestOneInput_s45.v, with its module paths changed; 1698 of its 1785 lines of code are new or changed and 818 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): segment S15 of the walk of the
   test harness's entry function LLVMFuzzerTestOneInput (_s23): from K85ac4 i (0x85ac4, m_split of segment i
   succeeded and v holds its parent and vid) through the duplicate scan of the model's VLAN table (the loop 0x85ad8
   <- 0x85b24, strcmp through the interceptor 0x43a14 when the vids agree, the 4-byte check 36 of mt[k].vid), the
   test against the table's capacity (cap), the copy of v into mt[mn] (checked_memcpy, 20 bytes) and the two
   counters, to the latch 0x859c4 .. 0x859f8 (v out of scope, the 4-byte check 33 of m->n) and on to K858f4 (i + 1)
   or K85bd0; or, when the table is full, through the -1 exit 0x85d44 .. 0x85d68 to K85bd0. Proves
   lt_seg_S15_stmt of LLVMFuzzerTestOneInput_defs.v.

   THE FORM: plugin-hostd/fuzz_command's lib/A/Prog/LLVMFuzzerTestOneInput_s42.v (origin/ossv/recipes
   501c0d516c69): seeds of symbolic states, the symbolic runs (plain where no check is crossed, by token where the
   two checks are), the calls taken through aj_art_at (strcmp, RtString.astrcmp_realizes, the interceptor-layer owner's row 17) and
   aj_intrin_atS (checked_memcpy), and the next cut applied to the run's last state. The internal points (stated in
   LLVMFuzzerTestOneInput_s23k.v, Section w): S15_LOOP j (0x85ad8, the scan's head after j entries), S15_X38
   (0x85b38, after the scan), S15_X40 (0x85b40, no duplicate) and S15_PJ (0x85b7c, the turn's model step done); each
   is stated relative to the K85ac4 state it came from (the same journal, the callee-saved registers, every byte
   outside the stack window below s1, the two counter slots and the entry mt[mn]).

   The proof: s23_top (K85ac4 i -> S15_LOOP 0 | S15_X40), s23l_step (S15_LOOP j -> S15_LOOP (j + 1) | S15_X38, the
   check 36 and the strcmp call), s23_x38 (S15_X38 -> S15_PJ | S15_X40), s23m_x40 (S15_X40 -> S15_PJ through the
   memcpy call | K85bd0 through the -1 exit), s23j_pj (S15_PJ -> the latch, check 33 -> K858f4 (i + 1) | K85bd0),
   s23_loop_all (the scan by induction down from 40 > cap) and s23_compose, which gives lt_seg_S15. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00 YG0q.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot PaSB PaArt PaLibF
PaLibH PaCallRun SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_c SegInstA
  LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s23k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ===== piece j ===== *)
(* ================= piece j: helpers that need no section variable ================= *)
(* a 64-bit word plus a literal (_s22's LLVMFuzzerTestOneInput_s22f.v:73-77, p6_w64_off) *)
Lemma s23j_w64_off : forall x y, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + y) = Z_to_bv 64 (x + y).
Proof.
intros x y. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Zplus_mod, Zmod_mod, <- Zplus_mod. reflexivity.
Qed.
(* &m->seg[i + 1] (s22f.v:97-98, p6_mseg_S) *)
Lemma s23j_mseg_S : forall m i, seg_spec.mseg_addr m (Datatypes.S i) = seg_spec.mseg_addr m i + 256.
Proof. intros m i. unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE. lia. Qed.
(* a register that holds an atom plus a literal *)
Lemma s23j_off : forall (regs : bvmap 5 word) (r : bv 5) E (n : nat) z v,
  getr regs r = sv_denot E (SOff n z) -> ew E n = Z_to_bv 64 v -> getr regs r = w64 (v + z).
Proof. intros regs r E n z v H Hn. rewrite H. cbn [sv_denot]. rewrite Hn. unfold w64. apply s23j_w64_off. Qed.
(* the three shadow bytes of v, 0xf8 each *)
Lemma s23j_f8 : forall (rd : reader) sh, sa_zs rd (sh + 4) [248; 248; 248] ->
  forall j, 4 <= j < 7 -> rd (sh + j) = Some 0xf8.
Proof.
intros rd sh H j Hj.
replace (sh + j) with (sh + 4 + Z.of_nat (Z.to_nat (j - 4))) by lia.
rewrite (H (Z.to_nat (j - 4)) ltac:(cbn [length]; lia)).
assert (Hc : j = 4 \/ j = 5 \/ j = 6) by lia. destruct Hc as [-> | [-> | ->]]; reflexivity.
Qed.
(* 1-byte literal chunks read back as bytes (_s10's LLVMFuzzerTestOneInput_s10k.v:116-159, s10_c1 ..
   s10_zs_ok, over any segment list) *)
Definition s23j_c1 (c : YP09.chunk) (off : Z) : option Z :=
  match c with
  | YP09.mkChunk o (CVal w (SLit z)) =>
    if (Z.eqb o off && N.eqb w 1)%bool then Some (bv_unsigned (byte_of_word (Z_to_bv 64 z) 0)) else None
  | _ => None
  end.
Fixpoint s23j_lit1 (cs : list YP09.chunk) (off : Z) : option Z :=
  match cs with
  | [] => None
  | c :: cs' => match s23j_c1 c off with Some v => Some v | None => s23j_lit1 cs' off end
  end.
Fixpoint s23j_zs_b (cs : list YP09.chunk) (off : Z) (l : list Z) : bool :=
  match l with
  | [] => true
  | x :: l' => match s23j_lit1 cs off with Some v => Z.eqb v x && s23j_zs_b cs (off + 1) l' | None => false end
  end.
Lemma s23j_lit1_in : forall cs off v, s23j_lit1 cs off = Some v ->
  exists z, In (YP09.mkChunk off (CVal 1 (SLit z))) cs /\ v = bv_unsigned (byte_of_word (Z_to_bv 64 z) 0).
Proof.
induction cs as [|c cs IH]; intros off v H; cbn [s23j_lit1] in H; [discriminate H|].
destruct (s23j_c1 c off) as [v'|] eqn:Ec.
- injection H as <-. destruct c as [o cv]. destruct cv as [w e| len | len | d s len]; cbn [s23j_c1] in Ec;
  try discriminate Ec.
  destruct e; try discriminate Ec.
  destruct ((o =? off) && (w =? 1)%N)%bool eqn:Eb; [|discriminate Ec].
  apply andb_prop in Eb as [E1 E2]. apply Z.eqb_eq in E1. apply N.eqb_eq in E2. subst o w.
  injection Ec as <-. exists z. split; [left; reflexivity | reflexivity].
- destruct (IH off v H) as (z & Hin & Hv). exists z. split; [right; exact Hin | exact Hv].
Qed.
Lemma s23j_zs_ok : forall (segs : list Segment) E H mem base cs l off,
  Forall (YP09.chunk_ok segs E (mrestrict H mem) base) cs -> s23j_zs_b cs off l = true ->
  sa_zs (aview segs H mem) (base + off) l.
Proof.
intros segs E H mem base cs l. induction l as [|x l IH]; intros off Hc Hb i Hi; cbn [length] in Hi; [lia|].
cbn [s23j_zs_b] in Hb. destruct (s23j_lit1 cs off) as [v|] eqn:Ev; [|discriminate Hb].
apply andb_prop in Hb as [Hx Hl]. apply Z.eqb_eq in Hx. subst x.
destruct i as [|i].
- cbn [nth]. destruct (s23j_lit1_in cs off v Ev) as (z & Hin & ->).
  rewrite Forall_forall in Hc. destruct (Hc _ Hin 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
  cbn [YP09.c_off YP09.c_val YP09.cbyte sv_denot] in Hb1, Hb2. injection Hb1 as <-.
  rewrite Z.add_0_r in Hb2. unfold aview. rewrite Z.add_0_r, Hb2. reflexivity.
- cbn [nth]. replace (base + off + Z.of_nat (Datatypes.S i)) with ((base + (off + 1)) + Z.of_nat i) by lia.
  apply (IH (off + 1) Hc Hl i). lia.
Qed.
(* the symbolic state at 0x85b7c is the s1 seed (s23_s1_seed) with the frame's shadow added, its base atom 38
   (= SH(FR), the value of 144(s1)) and its bytes [4, 7) writable, and s7 pinned to -8 *)
Definition s23j_shr : YP09.region := fshadow_region 38 LT_FCLS 4 7 [].
Definition s23j_G0 : facts := mkFacts [] [] [].
(* the token seed at 0x859d0 (s22f.v:64-70): the slots 152(s1) and 184(s1) and the 4 bytes of m->n (atom 32) *)
Definition s23j_slots : YP09.region := YP09.mkRegion (Some 9%nat) 152 192 0 0
  [YP09.mkChunk 152 (CVal 8 (shw (SOff 16 seg_spec.MC_N))); YP09.mkChunk 184 (CVal 8 (SOff 16 seg_spec.MC_N))].
Definition s23j_mn : YP09.region := YP09.mkRegion (Some 16%nat) seg_spec.MC_N (seg_spec.MC_N + 4) 0 0
  [YP09.mkChunk seg_spec.MC_N (CVal 4 (SOff 32 0))].
Definition s23j_GB : facts := mkFacts [(15%nat, mkAF SB SB 0); (16%nat, PTR 4); (32%nat, mkAF 0 32 0)] [] [].
Definition s23j_SH : list shent := [mkSHE 16 seg_spec.MC_N (seg_spec.MC_N + 8)].
Ltac s23j_inl := cbn [In]; repeat (first [left; reflexivity | right]).

(* ===== piece l ===== *)
(* ---- piece l (_s23): the helpers of s23l_step that need no section variable ---- *)
(* the symbolic states of the turn: at 0x85ad8 the s1 slots of the kit's seed and mt[j].vid at s4 + 16 (atom 40),
   with the shadow entry of the 4-byte check of mt[j].vid at s3 (atom 19); at 0x85b00, after strcmp, 176(s1) *)
Definition s23l_rmt : YP09.region := YP09.mkRegion (Some 20%nat) 16 20 0 0 [YP09.mkChunk 16 (CVal 4 (SOff 40 0))].
Definition s23l_G : facts := mkFacts [(9%nat, mkAF 0x7fff7f800000 (2 ^ 47) 0); (15%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
  (19%nat, mkAF 4096 0x7fffff800000 0)] [] [].
Definition s23l_SH : list shent := [mkSHE 19 0 4].
Definition s23l_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition s23l_rC : YP09.region :=
  YP09.mkRegion (Some 9%nat) 176 184 0 0 [YP09.mkChunk 176 (CVal 8 (SLit SHADOW_OFF))].
Definition s23l_ssC : sstate := mkSS 0xdcc sr_atoms [s23l_rC] None (mkFacts [] [] []).
(* the signed 32-bit compare of the two vids (lw of mt[j].vid, sext.w of s2) is their equality *)
Lemma s23l_swrap32 : forall a, 0 <= a < 2 ^ 32 -> bv_swrap 32 a = if a <? 2 ^ 31 then a else a - 2 ^ 32.
Proof.
intros a Ha. unfold bv_swrap, bv_wrap.
replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity. replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
destruct (Z.ltb_spec a (2 ^ 31)).
- rewrite Z.mod_small by lia. lia.
- replace (a + 2 ^ 31) with ((a - 2 ^ 31) + 1 * 2 ^ 32) by lia. rewrite Z.mod_add by lia.
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma s23l_vid_ne : forall E a b, ew E 40 = Z_to_bv 64 a -> ew E 18 = Z_to_bv 64 b -> 0 <= a < 2 ^ 32 ->
  0 <= b < 2 ^ 31 ->
  branch_taken BC_NE (sv_denot E (SExt true 32 (SOff 40 0))) (sv_denot E (SAluw ALU_ADD (SOff 18 0) (SLit 0))) =
  negb (a =? b).
Proof.
intros E a b Ea Eb Ha Hb. rewrite branch_ne_U. f_equal.
rewrite U_SExt, (U_atom E 40 a Ea) by lia.
rewrite (U_of_S E (SAluw _ _ _)), S_SAluw, (U_atom E 18 b Eb), U_lit by lia.
cbn [zalu_raw]. change (2 ^ Z.of_N 32) with (2 ^ 32).
rewrite Z.mod_0_l, Z.add_0_r, (Z.mod_small a), (Z.mod_small b) by lia.
rewrite !s23l_swrap32 by lia.
destruct (Z.ltb_spec b (2 ^ 31)); [|lia].
unfold bv_wrap. replace (bv_modulus 64) with (2 ^ 64) by reflexivity.
unfold zcanon, M64. rewrite (Z.mod_small b) by lia.
destruct (Z.ltb_spec a (2 ^ 31)).
- rewrite Z.mod_small by lia. reflexivity.
- replace (a - 2 ^ 32) with ((a - 2 ^ 32 + 2 ^ 64) + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia.
  rewrite Z.mod_small by lia.
  destruct (Z.eqb_spec (a - 2 ^ 32 + 2 ^ 64) b); destruct (Z.eqb_spec a b); first [reflexivity | exfalso; lia].
Qed.
(* s8 |= the turn's test, as the code ORs the two words *)
Lemma s23l_or_b2z : forall x y : bool, zcanon (Z.lor (seg_spec.b2z x) (seg_spec.b2z y)) = seg_spec.b2z (y || x).
Proof. intros [|] [|]; reflexivity. Qed.
Lemma s23l_b2z_rng : forall x : bool, 0 <= seg_spec.b2z x < 2 ^ 64.
Proof. intros [|]; cbn; lia. Qed.
(* the turn's model step: entry j added to the duplicate scan *)
Lemma s23l_ex_ne : forall par vid (t : list (list Z * Z)) j, (j < length t)%nat -> snd (nth j t ([], 0)) <> vid ->
  existsb (s23_dup par vid) (firstn (Datatypes.S j) t) = existsb (s23_dup par vid) (firstn j t).
Proof.
intros par vid t j Hj Hne. rewrite (s23_existsb_S _ t j Hj).
change (s23_dup par vid (nth j t ([], 0))) with
  ((snd (nth j t ([], 0)) =? vid) && (SegModel.strcmp (fst (nth j t ([], 0))) par =? 0)).
rewrite (proj2 (Z.eqb_neq _ _) Hne). cbn [andb]. apply orb_false_r.
Qed.
Lemma s23l_ex_eq : forall par vid (t : list (list Z * Z)) j, (j < length t)%nat -> snd (nth j t ([], 0)) = vid ->
  existsb (s23_dup par vid) (firstn (Datatypes.S j) t) =
  existsb (s23_dup par vid) (firstn j t) || (SegModel.strcmp (fst (nth j t ([], 0))) par =? 0).
Proof.
intros par vid t j Hj Heq. rewrite (s23_existsb_S _ t j Hj).
change (s23_dup par vid (nth j t ([], 0))) with
  ((snd (nth j t ([], 0)) =? vid) && (SegModel.strcmp (fst (nth j t ([], 0))) par =? 0)).
rewrite Heq, Z.eqb_refl. reflexivity.
Qed.
(* a callee-saved register across a call (_s22's p1_pres, LLVMFuzzerTestOneInput_s22a.v:246-251) *)
Lemma s23l_pres : forall regs regs2 (r : bv 5), aregs_preserved regs regs2 -> acallee_saved (bv_unsigned r) ->
  getr regs2 r = getr regs r.
Proof. intros regs regs2 r HP Hr. pose proof (HP _ Hr) as H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Ltac s23l_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.
Ltac s23l_in := cbn [In]; repeat (first [left; reflexivity | right]).

(* ===== piece m ===== *)


Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
(* the allocator record's laws (a theorem of the kit), the walk's hypothesis of the listing's runtime record (its
   api_env), and the two runtime entries this segment calls, at the statement's FP state (neither returns at
   another) *)
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis TL : PALib B.
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG SS___asan_memcpy).
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strcmp).
Let RUNP := SRr_run_pi_AJ (PI := PI) B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ (PI := PI) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (PI := PI) B LAWS.
Let RUN := paj_run (PI := PI) B LAWS.
Let RUNTO := paj_run_to (PI := PI) B LAWS.
Let BR := paj_branch (PI := PI).

Section i.
Variable i : nat.
Hypothesis HK8 : LTA_K858f4 B MT (Datatypes.S i).
Hypothesis HKB : LTA_K85bd0 B MT.

(* ---- K85ac4 i: 0x85ac4 .. 0x85ad4, to the scan's head (mn > 0) or past it (mn = 0) ---- *)
Lemma s23_top : S15_LOOP B MT i 0 -> S15_X40 B MT i -> LT_K85ac4_stmt B MT i.
Proof.
intros HL0 HX40. unfold LT_K85ac4_stmt.
intros cx ly S W regs mem md k acc c m tab mt par vid HB HF0 Hi HC Hcb Hm Htab Hmt Hig Hsp R15 R18 R22 R23 R25 R26
  R27 Ha0 HSL Hcm Htabs Hv Hvid.
assert (CTX : s23_ctx B MT i cx ly S W regs mem md k acc c m tab mt par vid)
  by exact (conj HB (conj HF0 (conj Hi (conj HC (conj Hcb (conj Hm (conj Htab (conj Hmt (conj Hig (conj Hsp (conj R15 (conj R18 (conj R22 (conj R23 (conj R25 (conj R26 (conj R27 (conj Ha0 (conj HSL (conj Hcm (conj Htabs (conj Hv Hvid)))))))))))))))))))))).
destruct (s23_ctx_num B MT i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX)
  as (HAR & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & Bc & Bm & Btab & Bmt).
pose proof (s23_ctx_slots B MT i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX) as HS1.
pose proof HC as (HFR & _ & _ & _). pose proof HFR as (HJ & R2 & R3 & R4 & R8 & R9 & _).
pose proof asan_consts as (C1 & _).
destruct Bmt as (_ & Mt4 & _ & Mtc & _). destruct Bm as (_ & M4 & _ & Mc & _). destruct Btab as (_ & T4 & _ & Tc & _).
unfold x_tabn, x_mtn, seg_spec.RVLAN_SIZE, seg_spec.MVLAN_SIZE, seg_spec.SEG_M_SIZE in Tc, Mtc, Mc.
pose proof (HSL 104 (fst (x_decl cx i)) ltac:(apply in_or_app; right; cbn [In]; right; right; left; reflexivity))
  as H104.
pose proof (s23_rdword_range _ _ _ _ _ H104) as Ra0.
set (t := snd (x_decl cx i)) in *. set (a0 := fst (x_decl cx i)) in *.
assert (Hsh : 0 <= x_sh cx < 2 ^ 64)
  by (unfold x_sh, shadow_addr, SHADOW_OFF; pose proof (Z.div_pos (x_fr cx) 8); pose proof (Z.div_le_upper_bound (x_fr cx) 8 (2 ^ 50)); lia).
set (vals := s23_vals cx tab mt a0 (Z.of_nat (length t)) m ++ []).
set (G := mkFacts [(9%nat, mkAF 0x7fff7f800000 (2 ^ 47) 0); (15%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
  (37%nat, mkAF 0 39 0)] [] []).
assert (U9 : bv_unsigned (ew (s23_E regs vals) 9) = x_s1 cx)
  by (rewrite (s23_E_reg _ _ 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U15 : bv_unsigned (ew (s23_E regs vals) 15) = SHADOW_OFF)
  by (rewrite (s23_E_reg _ _ 15 15%bv eq_refl), R15; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (E37 : ew (s23_E regs vals) 37 = Z_to_bv 64 (Z.of_nat (length t)))
  by (exact (s23_E_val regs vals 5 ltac:(unfold A_TEXT; lia))).
assert (U37 : bv_unsigned (ew (s23_E regs vals) 37) = Z.of_nat (length t))
  by (rewrite E37; apply unsigned_lit_small; lia).
pose proof (s23_s1_seed LO_K85ac4 0 0 cx W regs mem tab mt a0 (Z.of_nat (length t)) m [] G
  HS1 R9 R15 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold FO_V; lia) ltac:(lia) ltac:(lia) Ra0 ltac:(lia) Hsh
  ltac:(lia) ltac:(intros o Ho; lia) eq_refl) as HS.
fold vals in HS.
assert (HG : facts_ok (s23_E regs vals) G).
{ split; [|split; exact I]. cbn [G f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U15, U37. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold SHADOW_OFF.
  repeat split; first [exact I | lia]. }
specialize (HS HG). clear HG.
remember (s23_E regs vals) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply s23_E_img).
assert (U37E : U E (SOff 37 0) = Z.of_nat (length t)) by (apply U_atom; [exact E37 | lia]).
assert (U0 : U E (SLit 0) = 0) by (apply U_lit; lia).
unfold cfg_at, w64. clear H104.
(* 0x85ac4 .. 0x85ac8: s5 = mn, then blez s5 *)
paj_run_sh RUNP HS HJ.
{ awr_ok_tac. }
pose proof (s23_ro_kept SEGS _ _ _ _ _ HFr eq_refl) as K1. clear HF HFr HG.
rename ms into msA.
psrr_branch_pi RUNP BR HS.
- (* mn = 0: past the scan, to 0x85b40 *)
  rewrite s23_br_ge, U37E, U0 in Hc by (rewrite ?U37E, ?U0; lia).
  apply Z.leb_le in Hc. assert (Ht0 : t = []) by (destruct t; [reflexivity | cbn in Hc; lia]).
  paj_run_to_sh RUNTOP HS HJ 0xe0c.
  { awr_ok_tac. }
  pose proof (s23_ro_kept SEGS _ _ _ _ _ HFr eq_refl) as K2. clear HF HFr HG.
  s23_mdv. pmkst HS.
  apply (HX40 cx ly S W regs mem md k acc c m tab mt par vid (ms_regs ms) (ms_mem ms) mdv CTX); fold t a0.
  + split; [exact HJ|]. split.
    * intros r Hr. unfold S23_RLK in Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<- | Hr]; [s23_kreg_goal HS HE|]). destruct Hr.
    * intros a _ _. rewrite K2. apply K1.
  + fold t. rewrite Ht0. reflexivity.
  + s23_vreg HS (21%bv : bv 5). apply U_atom; [exact E37 | lia].
- (* mn > 0: s8 = 0, s3 = &mt[0].vid, s4 = mt, to the scan's head *)
  rewrite s23_br_ge, U37E, U0 in Hc by (rewrite ?U37E, ?U0; lia).
  apply Z.leb_gt in Hc.
  paj_run_to_sh RUNTOP HS HJ 0xda4.
  { awr_ok_tac. }
  pose proof (s23_ro_kept SEGS _ _ _ _ _ HFr eq_refl) as K2. clear HF HFr HG.
  s23_mdv. pmkst HS.
  apply (HL0 cx ly S W regs mem md k acc c m tab mt par vid (ms_regs ms) (ms_mem ms) mdv CTX); fold t a0.
  + split; [exact HJ|]. split.
    * intros r Hr. unfold S23_RLK in Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<- | Hr]; [s23_kreg_goal HS HE|]). destruct Hr.
    * intros a _ _. rewrite K2. apply K1.
  + fold t. lia.
  + s23_vreg HS (19%bv : bv 5). rewrite Nat2Z.inj_0, Z.mul_0_r, Z.add_0_r.
    apply (U_atom_off E 35 mt 16); [rewrite HE; exact (s23_E_val regs vals 3 ltac:(unfold A_TEXT; lia)) | lia | lia].
  + s23_vreg HS (20%bv : bv 5). rewrite Nat2Z.inj_0, Z.mul_0_r, Z.add_0_r.
    apply (U_atom E 35 mt); [rewrite HE; exact (s23_E_val regs vals 3 ltac:(unfold A_TEXT; lia)) | lia].
  + s23_vreg HS (21%bv : bv 5). rewrite Nat2Z.inj_0, Z.sub_0_r. apply U_atom; [exact E37 | lia].
  + s23_vreg HS (24%bv : bv 5). rewrite firstn_O. cbn [existsb seg_spec.b2z]. apply U_lit. lia.
Qed.

(* ---- S15_X38 (0x85b38): s5 := mn; bnez s8: a duplicate goes to the join S15_PJ with turn i adding nothing,
   none goes to S15_X40 ---- *)
Lemma s23_br_ne : forall E a b, branch_taken BC_NE (sv_denot E a) (sv_denot E b) = negb (U E a =? U E b).
Proof.
intros E a b. cbn [branch_taken]. f_equal.
Qed.
Ltac s23_inl := repeat (first [left; reflexivity | right]).
Lemma s23_x38 : S15_PJ B MT i -> S15_X40 B MT i -> S15_X38 B MT i.
Proof.
intros HPJ HX40. unfold S15_X38.
intros cx ly S W regs0 mem0 md0 k acc c m tab mt par vid regs mem md CTX HREL R24.
destruct (s23_ctx_num B MT i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX)
  as (HAR0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & Bc & Bm & Btab & Bmt).
pose proof (s23_ctx_slots B MT i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX) as HS0.
pose proof CTX as (_ & _ & Hi & HC & _ & _ & _ & _ & Hig & Hsp & R15 & _ & _ & _ & _ & _ & _ & Ha0 & _ & _ & Htabs & _).
pose proof HC as (HFR & _ & _ & _). pose proof HFR as (_ & _ & _ & _ & _ & R9 & _).
pose proof HREL as (HJ & HRL & HK).
pose proof asan_consts as (C1 & _).
destruct Bmt as (_ & Mt4 & _ & Mtc & _). destruct Bm as (_ & M4 & _ & Mc & _). destruct Btab as (_ & T4 & _ & Tc & _).
unfold x_tabn, x_mtn, seg_spec.RVLAN_SIZE, seg_spec.MVLAN_SIZE, seg_spec.SEG_M_SIZE in Tc, Mtc, Mc.
destruct Htabs as (_ & _ & _ & _ & Hmtab & Hlen).
set (t := snd (x_decl cx i)) in *. set (a0 := fst (x_decl cx i)) in *.
(* the slots at the current state: the scan wrote only below s1 *)
assert (HS1 : lt_slots cx (rdW W mem) (s23_slots cx tab mt a0 (Z.of_nat (length t)) m)).
{ intros o v Hin. assert (Ho : 32 <= o <= 184).
  { unfold s23_slots in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- _; lia|]). destruct Hin. }
  apply (s23_kept_word (rdW W mem0)); [|exact (HS0 o v Hin)].
  intros x Hx. apply HK; [lia|]. unfold s23_scr. lia. }
pose proof (HS1 104 a0 ltac:(unfold s23_slots; cbn [In]; s23_inl)) as H104.
pose proof (HS1 120 (Z.of_nat (length t)) ltac:(unfold s23_slots; cbn [In]; s23_inl)) as H120.
pose proof (s23_rdword_range _ _ _ _ _ H104) as Ra0.
assert (R9' : getr regs 9 = w64 (x_s1 cx)) by (rewrite (HRL 9%bv ltac:(unfold S23_RLK; cbn [In]; s23_inl)); exact R9).
assert (R15' : getr regs 15 = w64 SHADOW_OFF) by (rewrite (HRL 15%bv ltac:(unfold S23_RLK; cbn [In]; s23_inl)); exact R15).
assert (Hsh : 0 <= x_sh cx < 2 ^ 64)
  by (unfold x_sh, shadow_addr, SHADOW_OFF; pose proof (Z.div_pos (x_fr cx) 8); pose proof (Z.div_le_upper_bound (x_fr cx) 8 (2 ^ 50)); lia).
set (b := existsb (s23_dup par vid) t) in *.
assert (Hex : existsb (s23_dup par vid) t = b) by reflexivity. clearbody b.
assert (Hb01 : 0 <= seg_spec.b2z b <= 1) by (destruct b; cbn; lia).
set (vals := s23_vals cx tab mt a0 (Z.of_nat (length t)) m ++ []).
set (G := mkFacts [(9%nat, mkAF 0x7fff7f800000 (2 ^ 47) 0); (15%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
  (24%nat, mkAF 0 1 0)] [] []).
assert (U9 : bv_unsigned (ew (s23_E regs vals) 9) = x_s1 cx)
  by (rewrite (s23_E_reg _ _ 9 9%bv eq_refl), R9'; apply unsigned_lit_small; lia).
assert (U15 : bv_unsigned (ew (s23_E regs vals) 15) = SHADOW_OFF)
  by (rewrite (s23_E_reg _ _ 15 15%bv eq_refl), R15'; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U24 : bv_unsigned (ew (s23_E regs vals) 24) = seg_spec.b2z b)
  by (rewrite (s23_E_reg _ _ 24 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
pose proof (s23_s1_seed 0xe04 0 0 cx W regs mem tab mt a0 (Z.of_nat (length t)) m [] G
  HS1 R9' R15' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold FO_V; lia) ltac:(lia) ltac:(lia) Ra0 ltac:(lia) Hsh
  ltac:(lia) ltac:(intros o Ho; lia) eq_refl) as HS.
fold vals in HS.
assert (HG : facts_ok (s23_E regs vals) G).
{ split; [|split; exact I]. cbn [G f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U15, U24. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold SHADOW_OFF.
  repeat split; first [exact I | lia]. }
specialize (HS HG). clear HG.
remember (s23_E regs vals) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply s23_E_img).
assert (U24E : U E (SOff 24 0) = seg_spec.b2z b)
  by (apply U_atom; [rewrite HE, (s23_E_reg _ _ 24 24%bv eq_refl), R24; reflexivity | lia]).
assert (U0 : U E (SLit 0) = 0) by (apply U_lit; lia).
assert (E37 : ew E 37 = Z_to_bv 64 (Z.of_nat (length t)))
  by (rewrite HE; exact (s23_E_val regs vals 5 ltac:(unfold A_TEXT; lia))).
unfold cfg_at, w64.
(* 0x85b38: s5 := 120(s1) = mn; then bnez s8 *)
paj_run_sh RUNP HS HJ.
{ awr_ok_tac. }
pose proof (s23_ro_kept SEGS _ _ _ _ _ HFr eq_refl) as K1. clear HF HFr HG.
rename ms into msA.
psrr_branch_pi RUNP BR HS.
- (* s8 <> 0: a duplicate; turn i adds nothing; the join *)
  rewrite s23_br_ne, U24E, U0 in Hc. destruct b eqn:Eb; [|cbn in Hc; discriminate].
  assert (HD : x_decl cx (Datatypes.S i) = x_decl cx i).
  { unfold x_decl. rewrite (s23_decl_step _ _ _ i par vid Hi Hig Hsp Ha0). cbv zeta.
    fold (x_decl cx i). fold t. rewrite Hex. unfold t. symmetry. apply surjective_pairing. }
  paj_run_to_sh RUNTOP HS HJ 0xe48.
  { awr_ok_tac. }
  pose proof (s23_ro_kept SEGS _ _ _ _ _ HFr eq_refl) as K2. clear HF HFr HG.
  s23_mdv. pmkst HS.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ s23_scr cx a -> rdW W (ms_mem ms) a = rdW W mem0 a)
    by (intros a Ha Hs; rewrite K2, K1; exact (HK a Ha Hs)).
  apply (HPJ cx ly S W regs0 mem0 md0 k acc c m tab mt par vid (ms_regs ms) (ms_mem ms) mdv CTX); rewrite ?HD; fold t a0.
  + split; [exact HJ|]. split.
    * intros r Hr. unfold S23_RLKJ in Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<- | Hr];
        [match goal with |- getr _ ?r = _ => rewrite <- (HRL r ltac:(unfold S23_RLK; cbn [In]; s23_inl)) end;
         s23_kreg_goal HS HE|]).
      destruct Hr.
    * intros a Ha HD0. apply KM; [exact Ha|]. intros Hs. apply HD0. left. exact Hs.
  + exact Ha0.
  + apply (s23_kept_word (rdW W mem)); [|exact H104]. intros x Hx. rewrite K2, K1. reflexivity.
  + apply (s23_kept_word (rdW W mem)); [|exact H120]. intros x Hx. rewrite K2, K1. reflexivity.
  + apply (s23_kept_mtab (rdW W mem0)); [|exact Hmtab]. intros x Hx. apply KM; [lia|]. unfold s23_scr, ESTACK. lia.
  + exact Hlen.
- (* s8 = 0: no duplicate; past the join to S15_X40 *)
  rewrite s23_br_ne, U24E, U0 in Hc. destruct b eqn:Eb; [cbn in Hc; discriminate|].
  paj_run_to_sh RUNTOP HS HJ 0xe0c.
  { awr_ok_tac. }
  pose proof (s23_ro_kept SEGS _ _ _ _ _ HFr eq_refl) as K2. clear HF HFr HG.
  s23_mdv. pmkst HS.
  apply (HX40 cx ly S W regs0 mem0 md0 k acc c m tab mt par vid (ms_regs ms) (ms_mem ms) mdv CTX); fold t.
  + split; [exact HJ|]. split.
    * intros r Hr. unfold S23_RLK in Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<- | Hr];
        [match goal with |- getr _ ?r = _ => rewrite <- (HRL r ltac:(unfold S23_RLK; cbn [In]; s23_inl)) end;
         s23_kreg_goal HS HE|]).
      destruct Hr.
    * intros a Ha Hs. rewrite K2, K1. exact (HK a Ha Hs).
  + exact Hex.
  + s23_vreg HS (21%bv : bv 5). apply U_atom; [exact E37 | lia].
Qed.

(* ===== piece j ===== *)
(* ---- piece j: S15_PJ, 0x85b7c .. 0x85b8c (s5 := SH(FR), a6 := m, s8 := tab, s4 := 4) and the latch 0x859c4 ..
   0x859f8 (v out of scope: the frame's shadow bytes 4 .. 6 := 0xf8; check 33 of m->n as a token run; the four
   counter adds; blt s9, m->n) to K858f4 (i + 1) or K85bd0. A plain run 0x85b7c .. 0x859cc over the s1 seed with
   the frame's shadow added (s7 pinned to -8), then _s22's token seed at 0x859d0 (s22f.v:433-552) run to the
   blt and, on each arm, to the cut. The cut facts come from s23_end, at the state after the stores (for the
   token seed) and at the cut; 104(s1), 120(s1) and mt's table from S15_PJ's premises. ---- *)
Lemma s23j_pj : S15_PJ B MT i.
Proof.
intros cx ly S W regs0 mem0 md0 k acc c m tab mt par vid regs mem md CTX REL Hpos H104 H120 Hmtab Hlen.
destruct (s23_ctx_num B MT i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX)
  as (HAR0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & Bc & Bm & Btab & Bmt).
pose proof (s23_ctx_slots B MT i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX) as HSL0.
pose proof CTX as (HB & HF0 & Hi & HC & _ & _ & _ & _ & _ & _ & R15 & _ & R22 & R23 & R25 & R26 & R27 & _).
pose proof HC as (HFR & _ & _ & _). pose proof HFR as (_ & _ & _ & _ & _ & R9 & _).
destruct REL as (HJ & HRK & HKM).
pose proof asan_consts as (C1 & _).
pose proof Bm as (HIm & Hm4 & Hm16 & Hmc & Hma).
pose proof Btab as (_ & Ht4 & _ & Htc & _).
pose proof Bmt as (_ & Hmt4 & _ & Hmtc & Hmta).
unfold x_tabn, x_mtn, seg_spec.RVLAN_SIZE, seg_spec.MVLAN_SIZE, seg_spec.SEG_M_SIZE in Htc, Hmtc, Hmc.
(* the frame's shadow lies in the shadow band: apart from the stack, the heap blocks and the image *)
assert (Hsh : SHADOW_OFF <= x_sh cx /\ x_sh cx + 64 <= SHADOW_OFF + 2 ^ 44 - 960).
{ unfold x_sh, shadow_addr. pose proof (Z.div_pos (x_fr cx) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_upper_bound (x_fr cx) 8 (2 ^ 44 - 1024) ltac:(lia) ltac:(lia)). lia. }
unfold SHADOW_OFF in Hsh.
assert (Hshr : 0 <= x_sh cx < 2 ^ 64) by lia.
assert (OUTA : forall p len a, in_app p len -> p <= a < p + len -> ~ (x_sh cx + 4 <= a < x_sh cx + 7)).
{ intros p len a (Hp & Hor) Ha. unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hor.
  destruct Hor as [Hq | [Hq1 Hq2]]; lia. }
assert (OUTS : forall a, x_s1 cx <= a -> ~ (x_sh cx + 4 <= a < x_sh cx + 7)).
{ intros a Ha. lia. }
(* the s1 slots outside the two counters are those of K85ac4 *)
assert (KST : forall a, (x_s1 cx <= a < x_s1 cx + 104 \/ x_s1 cx + 112 <= a < x_s1 cx + 120 \/
    x_s1 cx + 128 <= a < x_s1 cx + 192) -> rdW W mem a = rdW W mem0 a).
{ intros a Ha. apply HKM; [clear - Ha N1 N2 C1; lia|].
  unfold s23_D0, s23_scr, ESTACK. clear - Ha N1 N2 N13 Hmtc C1. lia. }
assert (HSL : lt_slots cx (rdW W mem) (s23_slots cx tab mt (fst (x_decl cx (Datatypes.S i)))
    (Z.of_nat (length (snd (x_decl cx (Datatypes.S i))))) m)).
{ intros o v Hin. unfold s23_slots in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <-;
    first [exact H104 | exact H120 |
      apply (s23_kept_word (rdW W mem0)); [intros x Hx; apply KST; lia |
        apply HSL0; unfold s23_slots; s23j_inl]] |]).
  destruct Hin. }
pose proof (s23_rdword_range _ _ _ _ _ H104) as Ra.
pose proof (s23_rdword_range _ _ _ _ _ H120) as Rn.
assert (R9' : getr regs 9 = w64 (x_s1 cx)) by (rewrite HRK by (unfold S23_RLKJ; s23j_inl); exact R9).
assert (R15' : getr regs 15 = w64 SHADOW_OFF) by (rewrite HRK by (unfold S23_RLKJ; s23j_inl); exact R15).
assert (R23' : getr regs 23 = w64 (-8)) by (rewrite HRK by (unfold S23_RLKJ; s23j_inl); exact R23).

(* ---------------- the plain run 0x85b7c .. 0x859cc ---------------- *)
set (vals := s23_vals cx tab mt (fst (x_decl cx (Datatypes.S i))) (Z.of_nat (length (snd (x_decl cx (Datatypes.S i)))))
  m ++ []).
pose proof (s23_s1_seed 0xe48 0 0 cx W regs mem tab mt _ _ m [] s23j_G0 HSL R9' R15'
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold FO_V; lia) ltac:(lia) ltac:(lia) Ra Rn Hshr ltac:(lia)
  ltac:(intros o Ho; lia) eq_refl) as HS.
fold vals in HS.
specialize (HS ltac:(split; [exact I | split; exact I])).
remember (s23_E regs vals) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply s23_E_img).
assert (E38 : ew E 38 = Z_to_bv 64 (x_sh cx)) by (rewrite HE; exact (s23_E_val regs vals 6 ltac:(unfold A_TEXT; lia))).
assert (U38 : bv_unsigned (ew E 38) = x_sh cx) by (rewrite E38; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = x_s1 cx)
  by (rewrite HE, (s23_E_reg _ _ 9 9%bv eq_refl), R9'; apply unsigned_lit_small; lia).
pose proof (proj1 HJ) as HAR.
assert (Hfin : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite N6; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ LT_FCLS (x_fpos cx) HAR Hfin) as (_ & _ & _ & HFSpres).
rewrite N7 in HFSpres. change (fs_frame_bytes LT_FCLS / 8) with 64 in HFSpres.
assert (HR : region_ok SEGS E (mrestrict (w_H W) mem) s23j_shr).
{ unfold region_ok, s23j_shr, fshadow_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  change (fs_frame_bytes LT_FCLS / 8) with 64. rewrite U38.
  split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. apply (apresent_writable SEGS). unfold x_sh. exact (proj1 (HFSpres o ltac:(lia))). }
assert (HD : all_disjoint E s23j_shr [s1_region 0 0]).
{ cbn [all_disjoint]. split; [|exact I]. unfold extent_disjoint, s23j_shr, fshadow_region, s1_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U38, U9. change (fs_frame_bytes LT_FCLS / 8) with 64.
  left. lia. }
pose proof (st_ok_pi_add_region E _ _ s23j_shr HS eq_refl HR HD) as HS1. clear HS.
pose proof (st_ok_pi_pin_reg' E _ _ 23%bv (-8) HS1 R23' eq_refl) as HS. clear HS1.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
unfold cfg_at, w64.
paj_run_to_sh RUNTOP HS HJ 0xc9c.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_gen with (n := 38%nat) (b := x_sh cx); [reflexivity | exact U38 | | awr_ok_tac].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
  right; right; right; left. exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|].
  right. rewrite N7. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes LT_FCLS / 8) with 64.
  unfold x_sh in Ha. lia. }
rename ms into msA. s23_mdv. rename mdv into mdA. cbn [ms_mem mkst] in HFr.
clear HF HG HR HD HAR HFSpres.
(* every byte but v's three shadow bytes is as at 0x85b7c *)
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 4 <= a < x_sh cx + 7) -> rdW W (ms_mem msA) a = rdW W mem a).
{ intros a Ha Hna.
  apply (kept_of_frame (segs := SEGS) E _ (w_H W) mem (ms_mem msA) (fun y => x_sh cx + 4 <= y < x_sh cx + 7) HFr);
    [| exact Ha | exact Hna].
  intros b wlo whi a' Hin Hr.
  lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in
    replace l with l' in Hin by (vm_compute; reflexivity) end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?U38 in Hr; lia |]).
  destruct Hin. }
(* the registers at 0x859d0 *)
assert (AK : forall r : bv 5, In r ([2; 3; 4; 8; 9; 15; 22; 25; 26; 27]%bv : list (bv 5)) ->
  getr (ms_regs msA) r = getr regs0 r).
{ intros r Hr. rewrite <- (HRK r) by (unfold S23_RLKJ; cbn [In] in Hr |- *; tauto).
  cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [s23_kreg_goal HS HE|]). destruct Hr. }
assert (A16 : getr (ms_regs msA) 16 = w64 m).
{ s23_vreg HS (16%bv : bv 5).
  apply (U_atom E 39 m); [rewrite HE; exact (s23_E_val regs vals 7 ltac:(unfold A_TEXT; lia)) | lia]. }
assert (A20 : getr (ms_regs msA) 20 = w64 4) by (s23_vreg HS (20%bv : bv 5); apply U_lit; lia).
assert (A21 : getr (ms_regs msA) 21 = w64 (x_sh cx)) by (s23_vreg HS (21%bv : bv 5); apply (U_atom E 38 _ E38); lia).
assert (A24 : getr (ms_regs msA) 24 = w64 tab).
{ s23_vreg HS (24%bv : bv 5).
  apply (U_atom E 34 tab); [rewrite HE; exact (s23_E_val regs vals 2 ltac:(unfold A_TEXT; lia)) | lia]. }
assert (A23 : getr (ms_regs msA) 23 = w64 (-8)).
{ let P := fresh "P" in s23_prraw HS (23%bv : bv 5) P; rewrite P; reflexivity. }
(* v's three shadow bytes, read back from the region's chunks *)
assert (HZS3 : sa_zs (rdW W (ms_mem msA)) (x_sh cx + 4) [248; 248; 248]).
{ lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
    pose proof (PaLibG.st_ok_pi_region_nth E ssx (restrict (w_H W) msA) 0%nat r0 HS
      ltac:(vm_compute; reflexivity)) as RSH end.
  destruct RSH as (_ & _ & _ & CSH).
  cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in CSH. rewrite U38 in CSH.
  exact (s23j_zs_ok SEGS E (w_H W) (ms_mem msA) (x_sh cx) _ [248; 248; 248] 4 CSH ltac:(vm_compute; reflexivity)). }
(* the cut facts at 0x859d0 (for the token seed) *)
assert (KMA : forall a, 0 <= a < 2 ^ 64 -> ~ s23_D0 cx mt (length (snd (x_decl cx i))) a ->
  ~ (x_sh cx + 4 <= a < x_sh cx + 7) -> rdW W (ms_mem msA) a = rdW W mem0 a).
{ intros a Ha HD Hn. rewrite (KA a Ha Hn). exact (HKM a Ha HD). }
assert (HmtA : sa_mtab (rdW W (ms_mem msA)) mt (snd (x_decl cx (Datatypes.S i)))).
{ apply (s23_kept_mtab (rdW W mem)); [|exact Hmtab]. intros x Hx. apply KA; [lia|].
  apply (OUTA mt (x_mtn cx)); [exact Hmta | unfold x_mtn, seg_spec.MVLAN_SIZE; lia]. }
destruct (s23_end B MT i cx ly S W regs0 mem0 md0 k acc c m tab mt par vid (ms_regs msA) (ms_mem msA) mdA
  (snd (x_decl cx (Datatypes.S i))) CTX HJ
  (AK 2%bv ltac:(s23j_inl)) (AK 3%bv ltac:(s23j_inl)) (AK 4%bv ltac:(s23j_inl)) (AK 8%bv ltac:(s23j_inl))
  (AK 9%bv ltac:(s23j_inl)) KMA (s23j_f8 _ _ HZS3) HmtA Hlen) as (_ & _ & _ & _ & _ & HcmA & _ & HslA).
pmkst HS. clear HS HFr.

(* ---------------- the token run 0x859d0 .. 0x859f4 (_s22's seed B) ---------------- *)
set (nval := Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))).
assert (HMNA : sa_val (rdW W (ms_mem msA)) (m + seg_spec.MC_N) 4 nval)
  by exact (proj1 (s23_mconf_n _ _ _ (proj2 HcmA))).
assert (HN32 : (length (SegModel.mc_seg (x_mcF cx)) <= 32)%nat) by exact (proj2 (s23_mconf_n _ _ _ (proj2 HcmA))).
assert (Hnval : 0 <= nval <= 32) by (unfold nval; lia).
assert (Hilt : Z.of_nat i < nval) by (unfold nval; lia).
remember (s23_E (ms_regs msA) [nval]) as EB eqn:HEB.
assert (HEIB : img_env VAL A_LIM EB) by (rewrite HEB; apply s23_E_img).
assert (EBK : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r ->
  In r ([2; 3; 4; 8; 9; 15; 22; 25; 26; 27]%bv : list (bv 5)) -> ew EB n = getr regs0 r).
{ intros n r Hn Hr. rewrite HEB, (s23_E_reg _ _ n r Hn). exact (AK r Hr). }
assert (EB9 : bv_unsigned (ew EB 9) = x_s1 cx).
{ rewrite (EBK 9%nat 9%bv eq_refl ltac:(s23j_inl)), R9. apply unsigned_lit_small. lia. }
assert (EB15 : ew EB 15 = Z_to_bv 64 SHADOW_OFF) by exact (eq_trans (EBK 15%nat 15%bv eq_refl ltac:(s23j_inl)) R15).
assert (EB16 : ew EB 16 = Z_to_bv 64 m) by (rewrite HEB, (s23_E_reg _ _ 16 16%bv eq_refl); exact A16).
assert (EB32 : ew EB 32 = Z_to_bv 64 nval)
  by (rewrite HEB; exact (s23_E_val (ms_regs msA) [nval] 0 ltac:(unfold A_TEXT; lia))).
assert (UB15 : U EB (SOff 15 0) = SHADOW_OFF) by (apply U_atom; [exact EB15 | unfold SHADOW_OFF; lia]).
assert (UB15' : bv_unsigned (ew EB 15) = SHADOW_OFF) by (rewrite EB15; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (UB16 : bv_unsigned (ew EB 16) = m) by (rewrite EB16; apply unsigned_lit_small; lia).
assert (UB32 : bv_unsigned (ew EB 32) = nval) by (rewrite EB32; apply unsigned_lit_small; lia).
assert (Hw152 : rdword (rdW W (ms_mem msA)) (x_s1 cx + 152) = Some (shadow_addr (m + seg_spec.MC_N)))
  by (apply HslA; apply in_or_app; right; s23j_inl).
assert (Hw184 : rdword (rdW W (ms_mem msA)) (x_s1 cx + 184) = Some (m + seg_spec.MC_N))
  by (apply HslA; apply in_or_app; left; unfold LT_LV; s23j_inl).
assert (Hshw : 0 <= shadow_addr (m + seg_spec.MC_N) < 2 ^ 62).
{ unfold shadow_addr, SHADOW_OFF, seg_spec.MC_N. pose proof (Z.div_pos (m + 0x2000) 8).
  pose proof (Z.div_le_upper_bound (m + 0x2000) 8 (2 ^ 59)). lia. }
assert (HSHW : sv_denot EB (shw (SOff 16 seg_spec.MC_N)) = Z_to_bv 64 (shadow_addr (m + seg_spec.MC_N))).
{ apply s23_denot_of_U; [|lia].
  apply (s23_U_shw EB 16 seg_spec.MC_N m EB16); [lia | unfold seg_spec.MC_N; lia | exact UB15]. }
assert (HS : st_ok_pi SEGS VAL EB (mkSS 0xc9c sr_atoms [s23j_slots; s23j_mn] None s23j_GB)
  (restrict (w_H W) (mkst (ms_regs msA) (Z_to_bv 64 (BASE + 0xc9c)) (ms_mem msA) (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - rewrite HEB. unfold s23_E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold region_ok, s23j_slots.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite EB9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val SEGS EB _ (x_s1 cx) 152 8 _ (shadow_addr (m + seg_spec.MC_N)) HSHW);
          [change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
        exact (val_mem_of_rdword SEGS (w_H W) (ms_mem msA) _ _ Hw152).
      * apply (chunk_ok_val SEGS EB _ (x_s1 cx) 184 8 (SOff 16 seg_spec.MC_N) (m + seg_spec.MC_N));
          [cbn [sv_denot]; rewrite UB16; reflexivity
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold seg_spec.MC_N; lia | lia |].
        exact (val_mem_of_rdword SEGS (w_H W) (ms_mem msA) _ _ Hw184).
    + unfold region_ok, s23j_mn.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite UB16. split; [unfold seg_spec.MC_N; lia|].
      split; [unfold seg_spec.MC_N; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS EB _ m seg_spec.MC_N 4 (SOff 32 0) nval);
        [cbn [sv_denot]; rewrite EB32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | lia |].
      change (N.to_nat 4) with 4%nat.
      exact (s23_val_mem_of SEGS (w_H W) (ms_mem msA) (m + seg_spec.MC_N) 4 nval HMNA).
  - apply pairwise_disjoint_of_extents.
    unfold s23j_slots, s23j_mn, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    cbn [base_val]. rewrite EB9, UB16. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split. right. unfold seg_spec.MC_N. lia.
  - split; [|split; [exact I | exact I]].
    cbn [s23j_GB f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite UB15', UB16, UB32. unfold SB. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. change (2 ^ 4) with 16.
    unfold SHADOW_OFF in *.
    repeat match goal with |- _ /\ _ => split end; first [exact Hm16 | lia]. }
assert (SHOK : sh_ok SEGS (SOff 15 0) s23j_SH EB (mrestrict (w_H W) (ms_mem msA))).
{ unfold sh_ok, s23j_SH. apply Forall_cons; [|apply Forall_nil].
  pose proof (req_size_pos seg_spec.SEG_M_SIZE ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as [_ Hrq].
  apply (shent_ok_of_range SEGS (w_H W) (ms_mem msA) EB (SOff 15 0) 16%nat m (req_size seg_spec.SEG_M_SIZE) m
    seg_spec.MC_N (seg_spec.MC_N + 8)).
  - exact (range_addressable_of_block SEGS B LAWS ly S W (ms_mem msA) mdA m seg_spec.SEG_M_SIZE m
      (req_size seg_spec.SEG_M_SIZE) (proj1 HJ) HIm ltac:(lia) ltac:(lia)).
  - exact UB15.
  - exact (U_atom EB 16%nat m EB16 ltac:(lia)).
  - unfold seg_spec.MC_N. lia.
  - unfold seg_spec.MC_N, seg_spec.SEG_M_SIZE in *. lia.
  - intros x Hx. change (Z.min seg_spec.MC_N (seg_spec.MC_N + 8)) with seg_spec.MC_N in Hx.
    change (Z.max seg_spec.MC_N (seg_spec.MC_N + 8)) with (seg_spec.MC_N + 8) in Hx.
    destruct Hma as (Hp & Hor).
    unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF, seg_spec.MC_N, seg_spec.SEG_M_SIZE in *.
    destruct Hor as [Hq | [Hq1 Hq2]]; lia. }
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac. }
rename ms into msB. s23_mdv. rename mdv into mdB. cbn [ms_mem mkst] in HFr.
assert (KB : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem msB) a = rdW W (ms_mem msA) a).
{ intros a Ha.
  apply (kept_of_frame (segs := SEGS) _ _ (w_H W) (ms_mem msA) (ms_mem msB) (fun _ : Z => False) HFr);
    [| exact Ha | intros []].
  intros b wlo whi a' Hin Hr.
  lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in
    replace l with l' in Hin by (vm_compute; reflexivity) end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr; exfalso; lia|]).
  destruct Hin. }
assert (EB25 : ew EB 25 = Z_to_bv 64 (Z.of_nat i)) by exact (eq_trans (EBK 25%nat 25%bv eq_refl ltac:(s23j_inl)) R25).
assert (UE25 : U EB (SOff 25 1) = Z.of_nat i + 1) by (apply (U_atom_off EB 25 _ 1 EB25); lia).
assert (UE32 : U EB (SOff 32 0) = nval) by (apply (U_atom EB 32 _ EB32); lia).
(* the memory facts at 0x859f4 that both cuts read *)
assert (KMB : forall a, 0 <= a < 2 ^ 64 -> ~ s23_D0 cx mt (length (snd (x_decl cx i))) a ->
  ~ (x_sh cx + 4 <= a < x_sh cx + 7) -> rdW W (ms_mem msB) a = rdW W mem0 a).
{ intros a Ha HD Hn. rewrite (KB a Ha). exact (KMA a Ha HD Hn). }
assert (HF8B : forall j, 4 <= j < 7 -> rdW W (ms_mem msB) (x_sh cx + j) = Some 0xf8).
{ intros j Hj. rewrite (KB (x_sh cx + j) ltac:(lia)). exact (s23j_f8 _ _ HZS3 j Hj). }
assert (HmtB : sa_mtab (rdW W (ms_mem msB)) mt (snd (x_decl cx (Datatypes.S i)))).
{ apply (s23_kept_mtab (rdW W (ms_mem msA))); [|exact HmtA]. intros x Hx. apply KB. lia. }
assert (KWB : forall o v, 0 <= o -> o + 8 <= 192 -> rdword (rdW W mem) (x_s1 cx + o) = Some v ->
  rdword (rdW W (ms_mem msB)) (x_s1 cx + o) = Some v).
{ intros o v Ho1 Ho2 Hw. apply (s23_kept_word (rdW W mem)); [|exact Hw]. intros x Hx.
  rewrite (KB x ltac:(lia)). apply KA; [lia | apply OUTS; lia]. }
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* blt taken: i + 1 < m->n, on to turn i + 1 at 0x858f4 *)
  rewrite s23_br_lt, UE25, UE32 in Hc by (rewrite ?UE25, ?UE32; lia). apply Z.ltb_lt in Hc.
  assert (HiS : (Datatypes.S i < length (SegModel.mc_seg (x_mcF cx)))%nat) by (unfold nval in Hc; lia).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan LO_K858f4.
  { awr_ok_tac. }
  rename ms into msK. s23_mdv. rename mdv into mdK. cbn [ms_mem mkst] in HFr.
  assert (KC : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem msK) a = rdW W (ms_mem msB) a).
  { intros a Ha.
    apply (kept_of_frame (segs := SEGS) _ _ (w_H W) (ms_mem msB) (ms_mem msK) (fun _ : Z => False) HFr);
      [| exact Ha | intros []].
    intros b wlo whi a' Hin Hr.
    lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in
      replace l with l' in Hin by (vm_compute; reflexivity) end.
    cbn [In] in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr; exfalso; lia|]).
    destruct Hin. }
  assert (FK : forall r : bv 5, In r ([2; 3; 4; 8; 9; 15; 16; 20; 21; 23; 24]%bv : list (bv 5)) ->
    getr (ms_regs msK) r = getr (ms_regs msA) r).
  { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [s23_kreg_goal HS HEB|]). destruct Hr. }
  assert (F2 : getr (ms_regs msK) 2 = getr regs0 2) by (rewrite FK by s23j_inl; apply AK; s23j_inl).
  assert (F3 : getr (ms_regs msK) 3 = getr regs0 3) by (rewrite FK by s23j_inl; apply AK; s23j_inl).
  assert (F4 : getr (ms_regs msK) 4 = getr regs0 4) by (rewrite FK by s23j_inl; apply AK; s23j_inl).
  assert (F8 : getr (ms_regs msK) 8 = getr regs0 8) by (rewrite FK by s23j_inl; apply AK; s23j_inl).
  assert (F9 : getr (ms_regs msK) 9 = getr regs0 9) by (rewrite FK by s23j_inl; apply AK; s23j_inl).
  assert (F15 : getr (ms_regs msK) 15 = w64 SHADOW_OFF) by (rewrite FK, AK by s23j_inl; exact R15).
  assert (F16 : getr (ms_regs msK) 16 = w64 m) by (rewrite FK by s23j_inl; exact A16).
  assert (F20 : getr (ms_regs msK) 20 = w64 4) by (rewrite FK by s23j_inl; exact A20).
  assert (F21 : getr (ms_regs msK) 21 = w64 (x_sh cx)) by (rewrite FK by s23j_inl; exact A21).
  assert (F23 : getr (ms_regs msK) 23 = w64 (-8)) by (rewrite FK by s23j_inl; exact A23).
  assert (F24 : getr (ms_regs msK) 24 = w64 tab) by (rewrite FK by s23j_inl; exact A24).
  assert (F22 : getr (ms_regs msK) 22 = w64 (seg_spec.mseg_addr m (Datatypes.S i))).
  { let P := fresh "P" in s23_prraw HS (22%bv : bv 5) P;
    rewrite (s23j_off _ _ _ _ _ (seg_spec.mseg_addr m i) P (eq_trans (EBK 22%nat 22%bv eq_refl ltac:(s23j_inl)) R22)).
    rewrite s23j_mseg_S. reflexivity. }
  assert (F27 : getr (ms_regs msK) 27 = w64 (seg_spec.mseg_addr m (Datatypes.S i))).
  { let P := fresh "P" in s23_prraw HS (27%bv : bv 5) P;
    rewrite (s23j_off _ _ _ _ _ (seg_spec.mseg_addr m i) P (eq_trans (EBK 27%nat 27%bv eq_refl ltac:(s23j_inl)) R27)).
    rewrite s23j_mseg_S. reflexivity. }
  assert (F25 : getr (ms_regs msK) 25 = w64 (Z.of_nat (Datatypes.S i))).
  { let P := fresh "P" in s23_prraw HS (25%bv : bv 5) P;
    rewrite (s23j_off _ _ _ _ _ (Z.of_nat i) P (eq_trans (EBK 25%nat 25%bv eq_refl ltac:(s23j_inl)) R25)).
    f_equal. lia. }
  assert (F26 : getr (ms_regs msK) 26 = w64 (- seg_spec.mseg_addr m (Datatypes.S i))).
  { let P := fresh "P" in s23_prraw HS (26%bv : bv 5) P;
    rewrite (s23j_off _ _ _ _ _ (- seg_spec.mseg_addr m i) P (eq_trans (EBK 26%nat 26%bv eq_refl ltac:(s23j_inl)) R26)).
    rewrite s23j_mseg_S. f_equal. lia. }
  assert (KMK : forall a, 0 <= a < 2 ^ 64 -> ~ s23_D0 cx mt (length (snd (x_decl cx i))) a ->
    ~ (x_sh cx + 4 <= a < x_sh cx + 7) -> rdW W (ms_mem msK) a = rdW W mem0 a).
  { intros a Ha HD Hn. rewrite (KC a Ha). exact (KMB a Ha HD Hn). }
  assert (HF8K : forall j, 4 <= j < 7 -> rdW W (ms_mem msK) (x_sh cx + j) = Some 0xf8).
  { intros j Hj. rewrite (KC (x_sh cx + j) ltac:(lia)). exact (HF8B j Hj). }
  assert (HmtK : sa_mtab (rdW W (ms_mem msK)) mt (snd (x_decl cx (Datatypes.S i)))).
  { apply (s23_kept_mtab (rdW W (ms_mem msB))); [|exact HmtB]. intros x Hx. apply KC. lia. }
  assert (KWK : forall o v, 0 <= o -> o + 8 <= 192 -> rdword (rdW W mem) (x_s1 cx + o) = Some v ->
    rdword (rdW W (ms_mem msK)) (x_s1 cx + o) = Some v).
  { intros o v Ho1 Ho2 Hw. apply (s23_kept_word (rdW W (ms_mem msB))); [|exact (KWB o v Ho1 Ho2 Hw)].
    intros x Hx. apply KC. lia. }
  destruct (s23_end B MT i cx ly S W regs0 mem0 md0 k acc c m tab mt par vid (ms_regs msK) (ms_mem msK) mdK
    (snd (x_decl cx (Datatypes.S i))) CTX HJ F2 F3 F4 F8 F9 KMK HF8K HmtK Hlen)
    as (HcoreK & HcK & HmK & HtK & HmtK' & HcmK & HtabsK & HslK).
  pmkst HS.
  change (SRr SEGS W (cfg_at SEGS (BASE + LO_K858f4) (ms_regs msK) (ms_mem msK) mdK) (lt_post B MT cx)).
  apply (HK8 fx cx ly S W (ms_regs msK) (ms_mem msK) mdK k acc c m tab mt HB HF0 HiS HcoreK HcK HmK HtK HmtK'
    F15 F16 F20 F21 F22 F23 F24 F25 F26 F27 Hpos); [|exact HcmK | exact HtabsK].
  intros o v Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
  + apply HslK. apply in_or_app. left. exact Hin.
  + cbn [In] in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <-;
      first [exact (KWK 104 _ ltac:(lia) ltac:(lia) H104) | exact (KWK 120 _ ltac:(lia) ltac:(lia) H120) |
             solve [apply HslK; apply in_or_app; right; s23j_inl]] |]).
    destruct Hin.
- (* blt not taken: i + 1 = m->n, j 0x85bd0, past the loop *)
  rewrite s23_br_lt, UE25, UE32 in Hc by (rewrite ?UE25, ?UE32; lia). apply Z.ltb_ge in Hc.
  assert (HSeq : (Datatypes.S i = length (SegModel.mc_seg (x_mcF cx)))%nat) by (unfold nval in Hc, Hilt; lia).
  assert (HMD : SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx) = x_decl cx (Datatypes.S i)).
  { unfold x_decl, SegModel.m_declared. rewrite HSeq, firstn_all. reflexivity. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan LO_K85bd0.
  { awr_ok_tac. }
  rename ms into msK. s23_mdv. rename mdv into mdK. cbn [ms_mem mkst] in HFr.
  assert (KC : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem msK) a = rdW W (ms_mem msB) a).
  { intros a Ha.
    apply (kept_of_frame (segs := SEGS) _ _ (w_H W) (ms_mem msB) (ms_mem msK) (fun _ : Z => False) HFr);
      [| exact Ha | intros []].
    intros b wlo whi a' Hin Hr.
    lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in
      replace l with l' in Hin by (vm_compute; reflexivity) end.
    cbn [In] in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr; exfalso; lia|]).
    destruct Hin. }
  assert (FK : forall r : bv 5, In r ([2; 3; 4; 8; 9; 16; 21; 24]%bv : list (bv 5)) ->
    getr (ms_regs msK) r = getr (ms_regs msA) r).
  { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [s23_kreg_goal HS HEB|]). destruct Hr. }
  assert (F2 : getr (ms_regs msK) 2 = getr regs0 2) by (rewrite FK by s23j_inl; apply AK; s23j_inl).
  assert (F3 : getr (ms_regs msK) 3 = getr regs0 3) by (rewrite FK by s23j_inl; apply AK; s23j_inl).
  assert (F4 : getr (ms_regs msK) 4 = getr regs0 4) by (rewrite FK by s23j_inl; apply AK; s23j_inl).
  assert (F8 : getr (ms_regs msK) 8 = getr regs0 8) by (rewrite FK by s23j_inl; apply AK; s23j_inl).
  assert (F9 : getr (ms_regs msK) 9 = getr regs0 9) by (rewrite FK by s23j_inl; apply AK; s23j_inl).
  assert (F16 : getr (ms_regs msK) 16 = w64 m) by (rewrite FK by s23j_inl; exact A16).
  assert (F21 : getr (ms_regs msK) 21 = w64 (x_sh cx)) by (rewrite FK by s23j_inl; exact A21).
  assert (F24 : getr (ms_regs msK) 24 = w64 tab) by (rewrite FK by s23j_inl; exact A24).
  assert (KMK : forall a, 0 <= a < 2 ^ 64 -> ~ s23_D0 cx mt (length (snd (x_decl cx i))) a ->
    ~ (x_sh cx + 4 <= a < x_sh cx + 7) -> rdW W (ms_mem msK) a = rdW W mem0 a).
  { intros a Ha HD Hn. rewrite (KC a Ha). exact (KMB a Ha HD Hn). }
  assert (HF8K : forall j, 4 <= j < 7 -> rdW W (ms_mem msK) (x_sh cx + j) = Some 0xf8).
  { intros j Hj. rewrite (KC (x_sh cx + j) ltac:(lia)). exact (HF8B j Hj). }
  assert (HmtK : sa_mtab (rdW W (ms_mem msK)) mt (snd (x_decl cx (Datatypes.S i)))).
  { apply (s23_kept_mtab (rdW W (ms_mem msB))); [|exact HmtB]. intros x Hx. apply KC. lia. }
  assert (KWK : forall o v, 0 <= o -> o + 8 <= 192 -> rdword (rdW W mem) (x_s1 cx + o) = Some v ->
    rdword (rdW W (ms_mem msK)) (x_s1 cx + o) = Some v).
  { intros o v Ho1 Ho2 Hw. apply (s23_kept_word (rdW W (ms_mem msB))); [|exact (KWB o v Ho1 Ho2 Hw)].
    intros x Hx. apply KC. lia. }
  destruct (s23_end B MT i cx ly S W regs0 mem0 md0 k acc c m tab mt par vid (ms_regs msK) (ms_mem msK) mdK
    (snd (x_decl cx (Datatypes.S i))) CTX HJ F2 F3 F4 F8 F9 KMK HF8K HmtK Hlen)
    as (HcoreK & HcK & HmK & HtK & HmtK' & HcmK & HtabsK & HslK).
  pmkst HS.
  change (SRr SEGS W (cfg_at SEGS (BASE + LO_K85bd0) (ms_regs msK) (ms_mem msK) mdK) (lt_post B MT cx)).
  apply (HKB fx cx ly S W (ms_regs msK) (ms_mem msK) mdK k acc c m tab mt HB HF0 HcoreK HcK HmK HtK HmtK'
    F16 F21 F24); [| exact HcmK | rewrite HMD; exact HtabsK].
  rewrite HMD, (Z.mod_small _ (2 ^ 64) Ra).
  intros o v Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <-;
    first [exact (KWK 104 _ ltac:(lia) ltac:(lia) H104) | exact (KWK 120 _ ltac:(lia) ltac:(lia) H120) |
           solve [apply HslK; apply in_or_app; left; unfold LT_LV; s23j_inl] |
           solve [apply HslK; apply in_or_app; right; s23j_inl]] |]).
  destruct Hin.
Qed.

(* ===== piece l ===== *)
(* ==== piece l: one turn of the duplicate scan of the model's VLAN table mt (0x85ad8 .. 0x85b24, BASE + 0xda4 ..
   0xdf0): the 4-byte check 36 of mt[j].vid at s3 (a token run with the shadow entry of mt's block), lw of mt[j].vid,
   the compare with s2 = vid; when the vids agree, strcmp(&mt[j], v) through the interceptor trampoline 0x43a14
   (aj_art_at with ASTRCMP) and a5 := 176(s1); s8 |= the test, s3 += 20, s4 += 20, s5 -= 1, and on to S15_X38
   (s5 = 0) or S15_LOOP (j + 1). ==== *)
(* the frame's object v = FR + 32 is usable for its 20 bytes under lt_fsh LFO_NV (_s22's s22e_v_addr,
   LLVMFuzzerTestOneInput_s22e.v:101-117) *)
Lemma s23l_v_addr : forall (rd : reader) F, F mod 8 = 0 -> sa_zs rd (shadow_addr F) (lt_fsh LFO_NV) ->
  range_addressable rd SHADOW_OFF (F + 32) 20.
Proof.
intros rd F HF HZ x Hx. unfold shadow_of_addr.
pose proof (HZ 4%nat ltac:(rewrite lt_fsh_len; lia)) as H4.
pose proof (HZ 5%nat ltac:(rewrite lt_fsh_len; lia)) as H5.
pose proof (HZ 6%nat ltac:(rewrite lt_fsh_len; lia)) as H6.
change (Z.of_nat 4) with 4 in H4. change (Z.of_nat 5) with 5 in H5. change (Z.of_nat 6) with 6 in H6.
change (nth 4 (lt_fsh LFO_NV) 0) with 0 in H4. change (nth 5 (lt_fsh LFO_NV) 0) with 0 in H5.
change (nth 6 (lt_fsh LFO_NV) 0) with 4 in H6.
unfold shadow_addr in H4, H5, H6.
destruct (Z_lt_le_dec x (F + 40)) as [Hl1|Hl1]; [|destruct (Z_lt_le_dec x (F + 48)) as [Hl2|Hl2]].
- exists 0. split; [|left; reflexivity]. replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + F / 8 + 4) by lia. exact H4.
- exists 0. split; [|left; reflexivity]. replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + F / 8 + 5) by lia. exact H5.
- exists 4. split; [replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + F / 8 + 6) by lia; exact H6|].
  right. lia.
Qed.
(* the shadow hull of v's first n <= 32 bytes is the frame's shadow word 0 (_s22's s22e_hull_v, :119-125) *)
Lemma s23l_hull_v : forall (rd : reader) F n, F mod 64 = 0 -> 0 <= F -> 0 < n <= 32 ->
  (forall j, 0 <= j < 8 -> rd (shadow_addr F + j) <> None) -> shadow_hull_vis rd (F + 32) n.
Proof.
intros rd F n HF HF0 Hn Hv s Hs.
assert (Hs' : shadow_addr F <= s < shadow_addr F + 8) by (unfold shadow_addr, SHADOW_OFF in *; lia).
replace s with (shadow_addr F + (s - shadow_addr F)) by lia. apply Hv. lia.
Qed.
(* a C string of the reader as the interceptors' byte string *)
Lemma s23l_astr : forall (W : world SEGS) mem p l, sa_strz (rdW W mem) p l -> astr_at SEGS W mem p (seg_spec.zb l).
Proof.
intros W mem p l H. destruct (sa_strz_bytes SEGS (w_H W) mem p l H) as (Hb & Hn0 & _).
split; [intros k Hk; exact (Hb k Hk) | exact Hn0].
Qed.
Lemma s23l_len_zb : forall l, astr_len (seg_spec.zb l) = Z.of_nat (length l).
Proof. intros l. unfold astr_len, seg_spec.zb. rewrite length_map. reflexivity. Qed.
(* the seed after strcmp (0x85b00): every register its own atom, 176(s1) the shadow base *)
Lemma s23l_seedC : forall (W : world SEGS) regs mem s1, getr regs 9 = w64 s1 -> 0 <= s1 -> s1 + 184 <= 2 ^ 64 ->
  rdword (rdW W mem) (s1 + 176) = Some SHADOW_OFF ->
  st_ok_pi SEGS VAL (s23_E regs []) s23l_ssC
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0xdcc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s1 R9 Hs0 Hs1 H176.
assert (U9 : bv_unsigned (ew (s23_E regs []) 9) = s1)
  by (rewrite (s23_E_reg _ _ 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
unfold s23l_ssC. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold s23_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold YP09.region_ok, s23l_rC.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (s23_chunk8 W mem _ s1 176 (SLit SHADOW_OFF) SHADOW_OFF H176); [unfold SHADOW_OFF; lia|].
  apply U_lit. unfold SHADOW_OFF. lia.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [exact I | split; exact I].
Qed.
(* the call of the strcmp interceptor trampoline (row 17, RtString.astrcmp_realizes) as a step of the walk's journal,
   through PaArt.aj_art_at (_s22's p1_strrchr_at, LLVMFuzzerTestOneInput_s22a.v:379-412) *)
Lemma s23l_strcmp_at : forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y sx sy (o : Z) raw,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> 0 < x -> 0 < y ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  astr_at SEGS W memT x sx -> astr_at SEGS W memT y sy ->
  aread_ok SEGS (2 * ESTACK) W regsT memT x (astr_len sx + 1) ->
  aread_ok SEGS (2 * ESTACK) W regsT memT y (astr_len sy + 1) ->
  atail_vis SEGS W memT (x + astr_len sx) -> atail_vis SEGS W memT (y + astr_len sy) ->
  rt_rom_view SEGS B W memT ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIG SS___interceptor_trampoline_strcmp)) memT (seg_rom SEGS)) mdc)
  (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
  aregs_preserved regsT regs2 /\ (getr regs2 10 = w64 0 <-> sx = sy) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> ~ False ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a)).
Proof.
intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y sx sy o raw
  HJ Ha0 Ha1 Hx Hy Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hsy Hrx Hry Htx Hty Hrom.
assert (ESTACK = 4096) as Hes by reflexivity.
apply (aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL) (2 * ESTACK) (fun _ => False) _ W regsT memT
  STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw (fun regs2 _ => getr regs2 10 = w64 0 <-> sx = sy)
  HJ Hsp Hal Hneg ltac:(lia) Hbud Hra (fun a F => False_ind _ F)).
apply (ASTRCMP fx lyc Sc W regsT memT mdc x y sx sy); try assumption.
apply (ecall_pre_stk_at SEGS B (2 * ESTACK) STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o HJ Hsp Hal Hneg
  ltac:(lia) Hbud); [rewrite Hra; exact Hraw | exact Hgp | exact Htp].
Qed.

(* a register the token runs left as its own atom: the K85ac4 state's (env E = s23_E regs _ behind the runs' fresh
   atoms 1024, 1025) *)
Ltac s23l_kreg HS HE RK :=
  lazymatch goal with |- getr _ ?r = getr _ ?r =>
    let P := fresh "P" in s23_prraw HS r P; apply (s23_reg_keep _ _ _ _ _ P);
    cbn [ew ewset Nat.eqb]; rewrite HE; etransitivity; [apply (s23_E_reg _ _ _ r); reflexivity|];
    apply RK; unfold S23_RLK; s23l_in
  end.
(* a register the plain runs after strcmp left as its own atom, callee-saved across the call *)
Ltac s23l_kregC HS HE2 HP3 TK RK :=
  lazymatch goal with |- getr _ ?r = getr _ ?r =>
    let P := fresh "P" in s23_prraw HS r P; apply (s23_reg_keep _ _ _ _ _ P);
    rewrite HE2; etransitivity; [apply (s23_E_reg _ _ _ r); reflexivity|];
    rewrite (s23l_pres _ _ r HP3) by s23l_cs; rewrite (TK r ltac:(s23l_in));
    apply RK; unfold S23_RLK; s23l_in
  end.
(* the call state's registers that the strcmp interceptor keeps *)
Ltac s23l_tk HS HE :=
  lazymatch goal with |- getr _ ?r = getr _ ?r =>
    let P := fresh "P" in prreg HS r P; rewrite P, HE; apply s23_E_reg; reflexivity
  end.
(* the machine state and the model a run left, named (each run's journal names the same model as the goal) *)
Ltac s23l_nm HS n d :=
  lazymatch type of HS with context [restrict _ ?m1] => rename m1 into n end;
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?x |} _ => set (d := x) in *; clearbody d end.

Lemma s23l_step : forall j, S15_X38 B MT i -> S15_LOOP B MT i (Datatypes.S j) -> S15_LOOP B MT i j.
Proof.
intros j HX38 HLS. unfold S15_LOOP.
intros cx ly S W regs0 mem0 md0 k acc c m tab mt par vid regs mem md CTX REL Hj R19 R20 R21 R24.
destruct (s23_ctx_num B MT i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX)
  as (HAR0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & Bc & Bm & Btab & Bmt).
pose proof (s23_ctx_slots B MT i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX) as HS1.
pose proof CTX as (HB & _ & Hi & HC & _ & _ & _ & _ & _ & Hsp & R15 & R18 & _ & _ & _ & _ & _ & Ha0 & _ & Hcm & Htabs
  & Hv & _).
pose proof HC as (HFR & HIMG & _ & _).
pose proof HFR as (_ & F2 & F3 & F4 & _ & F9 & _ & _ & _ & _ & _ & H176 & HZS).
destruct (s23_layout B MT LAWS cx ly S W regs0 mem0 md0 k LFO_NV HB HFR) as (L1 & _).
pose proof HB as (HPRE & _). pose proof HPRE as (_ & _ & _ & Hgp0 & Htp0 & _).
destruct REL as (HJ & RK & MK).
pose proof asan_consts as (C1 & _).
assert (WS : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
set (t := snd (x_decl cx i)) in *.
assert (Hj' : Z.of_nat j < Z.of_nat (length t)) by lia.
(* the blocks *)
pose proof Bmt as (Imt & Mt4 & _ & Mtc & Mta).
pose proof Btab as (_ & T4 & _ & Tc & _). pose proof Bm as (_ & M4 & _ & Mc & _).
unfold x_mtn, seg_spec.MVLAN_SIZE in Mtc, Mta. unfold x_tabn, seg_spec.RVLAN_SIZE in Tc.
unfold seg_spec.SEG_M_SIZE in Mc.
assert (RQmt : req_size (x_mtn cx) = 20 * (x_cap cx + 1)).
{ unfold req_size, x_mtn, seg_spec.MVLAN_SIZE. destruct (20 * (x_cap cx + 1) =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; lia|].
  reflexivity. }
(* the registers of the scan's head that are the K85ac4 state's *)
assert (G2 : getr regs 2 = w64 (x_s1 cx)) by (rewrite (RK 2%bv ltac:(unfold S23_RLK; s23l_in)); exact F2).
assert (G9 : getr regs 9 = w64 (x_s1 cx)) by (rewrite (RK 9%bv ltac:(unfold S23_RLK; s23l_in)); exact F9).
assert (G15 : getr regs 15 = w64 SHADOW_OFF) by (rewrite (RK 15%bv ltac:(unfold S23_RLK; s23l_in)); exact R15).
assert (G18 : getr regs 18 = w64 vid) by (rewrite (RK 18%bv ltac:(unfold S23_RLK; s23l_in)); exact R18).
assert (G3 : getr regs 3 = w64 (as_gp B)) by (rewrite (RK 3%bv ltac:(unfold S23_RLK; s23l_in)), F3; exact Hgp0).
assert (G4 : getr regs 4 = w64 (as_tp B)) by (rewrite (RK 4%bv ltac:(unfold S23_RLK; s23l_in)), F4; exact Htp0).
(* the bytes of the scan's head that are the K85ac4 state's: all but the window below s1 *)
assert (KL : forall a, 0 <= a < x_s1 cx - 2 * ESTACK -> rdW W mem a = rdW W mem0 a)
  by (intros a Ha; apply MK; [unfold ESTACK in Ha; lia | unfold s23_scr; lia]).
assert (KU : forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W mem a = rdW W mem0 a)
  by (intros a Ha; apply MK; [lia | unfold s23_scr; lia]).
(* entry j of the model's table, and the parent par in v *)
pose proof Htabs as (_ & _ & _ & _ & Hmtab & _).
destruct (s23_mtab_entry (rdW W mem0) mt t j Hmtab Hj) as (EZ & EN0 & EL16 & EVR & EVAL).
set (e := nth j t ([], 0)) in *.
assert (HNL : (length (SegModel.ms_name (x_seg cx i)) < 16)%nat).
{ destruct Hcm as [_ (bs & _ & Henc)]. destruct Henc as (_ & _ & Hsegs & _).
  destruct (Hsegs i Hi) as (_ & (_ & Hs16 & _) & _). exact Hs16. }
destruct (s23_split_props _ _ _ Hsp) as (Hvid1 & Hpl & _).
assert (HPL : (length par < 16)%nat) by lia.
clear HNL Hpl.
assert (HZt : sa_zs (rdW W mem) (mt + 20 * Z.of_nat j) (fst e ++ [0])).
{ apply (s23_kept_zs (rdW W mem0)); [|exact EZ]. rewrite length_app. cbn [length].
  intros x Hx. apply KL. clear - Hx Hj' N13 N12 Mtc Mt4 C1 N1 EL16. unfold ESTACK. lia. }
assert (HVt : sa_val (rdW W mem) (mt + 20 * Z.of_nat j + 16) 4 (snd e)).
{ apply (s23_kept_val (rdW W mem0)); [|exact EVAL].
  intros x Hx. apply KL. clear - Hx Hj' N13 N12 Mtc Mt4 C1 N1. unfold ESTACK. lia. }
assert (HPv : sa_strz (rdW W mem) (x_fr cx + FO_V) par).
{ apply (s23_kept_strz (rdW W mem0)); [|exact Hv].
  intros x Hx. apply KL. clear - Hx HPL N9 N10 N1 C1. unfold FO_V, ESTACK in *. lia. }
assert (HZSm : sa_zs (rdW W mem) (x_sh cx) (lt_fsh LFO_NV)).
{ apply (s23_kept_zs (rdW W mem0)); [|exact HZS]. rewrite lt_fsh_len.
  intros x Hx. apply KL. unfold x_sh, shadow_addr, SHADOW_OFF in *.
  pose proof (Z.div_le_upper_bound (x_fr cx) 8 (2 ^ 47)). pose proof (Z.div_pos (x_fr cx) 8).
  clear - Hx N9 N10 N1 C1 H H0. unfold ESTACK. lia. }
assert (HS1m : lt_slots cx (rdW W mem) (s23_slots cx tab mt (fst (x_decl cx i)) (Z.of_nat (length t)) m)).
{ intros o v Hin. assert (Ho : 0 <= o <= 184).
  { unfold s23_slots in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- _; lia|]). destruct Hin. }
  apply (s23_kept_word (rdW W mem0)); [|exact (HS1 o v Hin)]. intros x Hx. apply KU. lia. }
pose proof (HS1m 104 (fst (x_decl cx i)) ltac:(unfold s23_slots; s23l_in)) as H104.
pose proof (s23_rdword_range _ _ _ _ _ H104) as Ra0. clear H104.
assert (Hsh : 0 <= x_sh cx < 2 ^ 64)
  by (unfold x_sh, shadow_addr, SHADOW_OFF; pose proof (Z.div_pos (x_fr cx) 8); pose proof (Z.div_le_upper_bound (x_fr cx) 8 (2 ^ 50)); lia).
(* ---- the seed at 0x85ad8: the kit's s1 slots, with atom 40 = mt[j].vid, and the entry mt[j].vid at s4 + 16 ---- *)
set (vals := s23_vals cx tab mt (fst (x_decl cx i)) (Z.of_nat (length t)) m ++ [snd e]).
assert (U9 : bv_unsigned (ew (s23_E regs vals) 9) = x_s1 cx)
  by (rewrite (s23_E_reg _ _ 9 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (U15 : bv_unsigned (ew (s23_E regs vals) 15) = SHADOW_OFF)
  by (rewrite (s23_E_reg _ _ 15 15%bv eq_refl), G15; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U19 : bv_unsigned (ew (s23_E regs vals) 19) = mt + 16 + 20 * Z.of_nat j)
  by (rewrite (s23_E_reg _ _ 19 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew (s23_E regs vals) 20) = mt + 20 * Z.of_nat j)
  by (rewrite (s23_E_reg _ _ 20 20%bv eq_refl), R20; apply unsigned_lit_small; lia).
assert (E33 : ew (s23_E regs vals) 33 = Z_to_bv 64 (x_fr cx + FO_V))
  by exact (s23_E_val regs vals 1 ltac:(unfold A_TEXT; lia)).
assert (E40 : ew (s23_E regs vals) 40 = Z_to_bv 64 (snd e))
  by exact (s23_E_val regs vals 8 ltac:(unfold A_TEXT; lia)).
assert (HG : facts_ok (s23_E regs vals) s23l_G).
{ split; [|split; exact I]. cbn [s23l_G f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U15, U19. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold SHADOW_OFF.
  repeat split; first [exact I | lia]. }
pose proof (s23_s1_seed 0xda4 0 0 cx W regs mem tab mt (fst (x_decl cx i)) (Z.of_nat (length t)) m [snd e] s23l_G
  HS1m G9 G15 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold FO_V; lia) ltac:(lia) ltac:(lia) Ra0 ltac:(lia) Hsh
  ltac:(lia) ltac:(intros o Ho; lia) eq_refl HG) as HS0.
fold vals in HS0. clear HG.
assert (ROK : YP09.region_ok SEGS (s23_E regs vals) (mrestrict (w_H W) mem) s23l_rmt).
{ unfold YP09.region_ok, s23l_rmt.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U20.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (mt + 20 * Z.of_nat j) 16 4 (SOff 40 0) (snd e));
    [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | zside |].
  exact (s23_val_mem_of SEGS (w_H W) mem _ 4 _ HVt). }
assert (DJ : all_disjoint (s23_E regs vals) s23l_rmt [s1_region 0 0]).
{ cbn [all_disjoint]. unfold extent_disjoint, s23l_rmt, s1_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U20, U9. repeat split; lia. }
pose proof (st_ok_pi_add_region _ _ _ s23l_rmt HS0 eq_refl ROK DJ) as HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS. clear HS0 ROK DJ.
remember (s23_E regs vals) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply s23_E_img).
pose proof (proj1 HJ) as HAR.
assert (SHOK : sh_ok SEGS (SOff 15 0) s23l_SH E (mrestrict (w_H W) mem)).
{ unfold sh_ok, s23l_SH. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W) mem E (SOff 15 0) 19 (mt + 16 + 20 * Z.of_nat j) 4
    (mt + 16 + 20 * Z.of_nat j) 0 4).
  - apply (range_addressable_of_block SEGS B LAWS ly S W mem md mt (x_mtn cx)); [exact HAR | exact Imt | lia |].
    rewrite RQmt. lia.
  - apply U_atom; [rewrite HE, (s23_E_reg _ _ 15 15%bv eq_refl); exact G15 | unfold SHADOW_OFF; lia].
  - apply U_atom; [rewrite HE, (s23_E_reg _ _ 19 19%bv eq_refl); exact R19 | lia].
  - lia.
  - lia.
  - intros x Hx. change (Z.min 0 4) with 0 in Hx. change (Z.max 0 4) with 4 in Hx.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Mta. unfold SHADOW_OFF.
    clear - Hx Mta Hj' N13 N12. lia. }
unfold cfg_at, w64.
(* ---- 0x85ad8 .. 0x85af0: the check of mt[j].vid (token), a0 := mt[j].vid, a1 := sext.w s2; stops at bne ---- *)
paj_run_tok RUN HS HJ SHOK s23l_span.
{ awr_ok_tac. }
s23l_nm HS msA mdA. pose proof (s23_ro_kept SEGS _ _ _ _ _ HFr eq_refl) as K1. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK s23l_span.
- (* the vids differ: a0 := 0, s8 |= 0 *)
  rewrite (s23l_vid_ne _ (snd e) vid) in Hc;
    [| cbn [ew ewset Nat.eqb]; exact E40
     | cbn [ew ewset Nat.eqb]; rewrite HE, (s23_E_reg _ _ 18 18%bv eq_refl); exact G18 | lia | lia].
  apply negb_true_iff, Z.eqb_neq in Hc.
  pose proof (s23l_ex_ne par vid t j Hj Hc) as HEX.
  paj_run_tok RUN HS HJ SHOK s23l_span.
  { awr_ok_tac. }
  s23l_nm HS msB mdB. pose proof (s23_ro_kept SEGS _ _ _ _ _ HFr eq_refl) as K2. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK s23l_span.
  + (* s5 = 0: the scan is done, to 0x85b38 *)
    rewrite branch_eq_U in Hc0.
    rewrite (U_atom_off _ 21 (Z.of_nat (length t) - Z.of_nat j) (-1)) in Hc0
      by (first [lia | cbn [ew ewset Nat.eqb]; rewrite HE, (s23_E_reg _ _ 21 21%bv eq_refl); exact R21]).
    rewrite U_lit in Hc0 by lia. apply Z.eqb_eq in Hc0.
    paj_run_to_tok RUNTO HS HJ SHOK s23l_span 0xe04.
    { awr_ok_tac. }
    s23l_nm HS msC mdC. pose proof (s23_ro_kept SEGS _ _ _ _ _ HFr eq_refl) as K3. clear HF HFr HG.
    pmkst HS.
    apply (HX38 cx ly S W regs0 mem0 md0 k acc c m tab mt par vid (ms_regs msC) (ms_mem msC) mdC CTX).
    * split; [exact HJ|]. split.
      -- intros r Hr. unfold S23_RLK in Hr. cbn [In] in Hr.
         repeat (destruct Hr as [<- | Hr]; [s23l_kreg HS HE RK|]). destruct Hr.
      -- intros a Ha Hn. rewrite K3, K2, K1. exact (MK a Ha Hn).
    * change (snd (x_decl cx i)) with t.
      replace (existsb (s23_dup par vid) t) with (existsb (s23_dup par vid) (firstn (Datatypes.S j) t))
        by (rewrite firstn_all2 by lia; reflexivity).
      rewrite HEX.
      s23_vreg HS (24%bv : bv 5).
      rewrite U_SAlu, U_lit by lia.
      rewrite (U_atom _ 24 (seg_spec.b2z (existsb (s23_dup par vid) (firstn j t))))
        by (first [apply s23l_b2z_rng | cbn [ew ewset Nat.eqb]; rewrite HE, (s23_E_reg _ _ 24 24%bv eq_refl); exact R24]).
      cbn [zalu_raw]. rewrite Z.lor_0_l. apply zcanon_small. apply s23l_b2z_rng.
  + (* s5 <> 0: the next entry, back to 0x85ad8 *)
    rewrite branch_eq_U in Hc0.
    rewrite (U_atom_off _ 21 (Z.of_nat (length t) - Z.of_nat j) (-1)) in Hc0
      by (first [lia | cbn [ew ewset Nat.eqb]; rewrite HE, (s23_E_reg _ _ 21 21%bv eq_refl); exact R21]).
    rewrite U_lit in Hc0 by lia. apply Z.eqb_neq in Hc0.
    paj_run_to_tok RUNTO HS HJ SHOK s23l_span 0xda4.
    { awr_ok_tac. }
    s23l_nm HS msC mdC. pose proof (s23_ro_kept SEGS _ _ _ _ _ HFr eq_refl) as K3. clear HF HFr HG.
    pmkst HS.
    apply (HLS cx ly S W regs0 mem0 md0 k acc c m tab mt par vid (ms_regs msC) (ms_mem msC) mdC CTX).
    * split; [exact HJ|]. split.
      -- intros r Hr. unfold S23_RLK in Hr. cbn [In] in Hr.
         repeat (destruct Hr as [<- | Hr]; [s23l_kreg HS HE RK|]). destruct Hr.
      -- intros a Ha Hn. rewrite K3, K2, K1. exact (MK a Ha Hn).
    * change (snd (x_decl cx i)) with t. lia.
    * s23_vreg HS (19%bv : bv 5).
      rewrite (U_atom_off _ 19 (mt + 16 + 20 * Z.of_nat j) 20)
        by (first [lia | cbn [ew ewset Nat.eqb]; rewrite HE, (s23_E_reg _ _ 19 19%bv eq_refl); exact R19]).
      lia.
    * s23_vreg HS (20%bv : bv 5).
      rewrite (U_atom_off _ 20 (mt + 20 * Z.of_nat j) 20)
        by (first [lia | cbn [ew ewset Nat.eqb]; rewrite HE, (s23_E_reg _ _ 20 20%bv eq_refl); exact R20]).
      lia.
    * change (snd (x_decl cx i)) with t. s23_vreg HS (21%bv : bv 5).
      rewrite (U_atom_off _ 21 (Z.of_nat (length t) - Z.of_nat j) (-1))
        by (first [lia | cbn [ew ewset Nat.eqb]; rewrite HE, (s23_E_reg _ _ 21 21%bv eq_refl); exact R21]).
      lia.
    * change (snd (x_decl cx i)) with t. rewrite HEX.
      s23_vreg HS (24%bv : bv 5).
      rewrite U_SAlu, U_lit by lia.
      rewrite (U_atom _ 24 (seg_spec.b2z (existsb (s23_dup par vid) (firstn j t))))
        by (first [apply s23l_b2z_rng | cbn [ew ewset Nat.eqb]; rewrite HE, (s23_E_reg _ _ 24 24%bv eq_refl); exact R24]).
      cbn [zalu_raw]. rewrite Z.lor_0_l. apply zcanon_small. apply s23l_b2z_rng.
- (* the vids agree: strcmp(&mt[j], v) *)
  rewrite (s23l_vid_ne _ (snd e) vid) in Hc;
    [| cbn [ew ewset Nat.eqb]; exact E40
     | cbn [ew ewset Nat.eqb]; rewrite HE, (s23_E_reg _ _ 18 18%bv eq_refl); exact G18 | lia | lia].
  apply negb_false_iff, Z.eqb_eq in Hc.
  pose proof (s23l_ex_eq par vid t j Hj Hc) as HEX.
  (* 0x85af4 .. 0x85afc: a0 := s4 = &mt[j], a1 := 56(s1) = v, the jal of the strcmp trampoline *)
  paj_run_tok RUN HS HJ SHOK s23l_span.
  { awr_ok_tac. }
  s23l_nm HS msT mdT. pose proof (s23_ro_kept SEGS _ _ _ _ _ HFr eq_refl) as K2. clear HF HFr HG.
  pmkst HS.
  assert (KT : forall a, rdW W (ms_mem msT) a = rdW W mem a) by (intros a; rewrite K2; exact (K1 a)).
  assert (TK : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
    getr (ms_regs msT) r = getr regs r).
  { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [s23l_tk HS HE|]). destruct Hr. }
  prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
  rewrite HE, (s23_E_reg _ _ 20 20%bv eq_refl), R20 in P10. rewrite E33 in P11.
  assert (HspT : spZ (ms_regs msT) = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
  { unfold spZ. rewrite (TK 2%bv ltac:(s23l_in)), G2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
  assert (Ho16 : (x_s1 cx - x_sp0 cx) mod 16 = 0).
  { pose proof (Z.div_mod (x_s1 cx) 32 ltac:(lia)) as D1. rewrite N4 in D1.
    pose proof (Z.div_mod (x_sp0 cx) 16 ltac:(lia)) as D2. rewrite L1 in D2.
    replace (x_s1 cx - x_sp0 cx) with ((2 * (x_s1 cx / 32) - x_sp0 cx / 16) * 16) by lia. apply Z_mod_mult. }
  pose proof (proj1 HJ) as HART.
  destruct (al_blocks _ _ LAWS ly S W (ms_mem msT) mdT mt (x_mtn cx) HART Imt) as (_ & _ & _ & _ & HMpres & _ & _).
  rewrite RQmt in HMpres.
  assert (HFin : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite N6; left; reflexivity).
  destruct (al_frames _ _ LAWS ly S W (ms_mem msT) mdT LT_FCLS (x_fpos cx) HART HFin) as (_ & _ & HFpres & _).
  rewrite N7 in HFpres. change (fs_frame_bytes LT_FCLS) with 512 in HFpres.
  assert (HSx : sa_strz (rdW W (ms_mem msT)) (mt + 20 * Z.of_nat j) (fst e)).
  { split; [|exact EN0]. intros q Hq. rewrite KT. exact (HZt q Hq). }
  assert (HSy : sa_strz (rdW W (ms_mem msT)) (x_fr cx + FO_V) par).
  { destruct HPv as [Hz Hn0]. split; [|exact Hn0]. intros q Hq. rewrite KT. exact (Hz q Hq). }
  assert (HZST : sa_zs (rdW W (ms_mem msT)) (x_sh cx) (lt_fsh LFO_NV)) by (intros q Hq; rewrite KT; exact (HZSm q Hq)).
  assert (HF8 : x_fr cx mod 8 = 0).
  { pose proof (Z.div_mod (x_fr cx) 64 ltac:(lia)) as D. rewrite N8 in D.
    replace (x_fr cx) with ((x_fr cx / 64 * 8) * 8) by lia. apply Z_mod_mult. }
  destruct (sa_strz_bytes SEGS (w_H W) (ms_mem msT) _ _ HSx) as (_ & _ & Hzsx).
  destruct (sa_strz_bytes SEGS (w_H W) (ms_mem msT) _ _ HSy) as (_ & _ & Hzsy).
  assert (HROM : rt_rom_view SEGS B W (ms_mem msT)).
  { pose proof HIMG as (HRO & _ & _). intros a Hr Ho He.
    assert (Himg : in_img SEGS a) by (destruct Hr as (sg & Hsg & _ & Ha); exists sg; split; [exact Hsg | exact Ha]).
    pose proof (pa_img_range _ Himg) as HIR. unfold kImgEnd in HIR.
    rewrite KT, KL by (unfold ESTACK; lia). apply HRO; [left; exact Hr | exact Ho | exact He]. }
  eapply SRr_bind.
  { exact (s23l_strcmp_at W (ms_regs msT) (ms_mem msT) STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
      (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S mdT k
      (mt + 20 * Z.of_nat j) (x_fr cx + FO_V) (seg_spec.zb (fst e)) (seg_spec.zb par)
      (x_s1 cx - x_sp0 cx) (Z_to_bv 64 (BASE + 0xdcc)) HJ P10 P11 ltac:(lia) ltac:(unfold FO_V; lia)
      HspT Ho16 ltac:(lia) ltac:(rewrite WS; unfold ESTACK; lia)
      ltac:(rewrite (TK 3%bv ltac:(s23l_in)); exact G3) ltac:(rewrite (TK 4%bv ltac:(s23l_in)); exact G4)
      P1 ltac:(apply ret_ok_codeptr_v; [lia | reflexivity])
      (s23l_astr W (ms_mem msT) _ _ HSx) (s23l_astr W (ms_mem msT) _ _ HSy)
      ltac:(rewrite s23l_len_zb; apply (aread_ok_of_block SEGS B LAWS (2 * ESTACK) ly S W (ms_regs msT) (ms_mem msT)
              mdT mt (x_mtn cx) _ _ HART Imt); [lia | unfold x_mtn, seg_spec.MVLAN_SIZE; lia | lia |];
            rewrite HspT; unfold ESTACK; lia)
      ltac:(rewrite s23l_len_zb; unfold aread_ok;
            split; [unfold FO_V; lia|]; split; [unfold FO_V; lia|]; split; [lia|]; split;
            [ intros a Ha; split;
              [ destruct HSy as [Hz _];
                pose proof (Hz (Z.to_nat (a - (x_fr cx + FO_V))) ltac:(rewrite length_app; cbn [length]; lia)) as Hb;
                rewrite Z2Nat.id in Hb by lia;
                replace (x_fr cx + FO_V + (a - (x_fr cx + FO_V))) with a in Hb by lia;
                rewrite Hb; discriminate
              | unfold ascratch_stk; rewrite HspT; unfold FO_V, ESTACK in *; lia ] |];
            split;
            [ apply amem_range_high; [lia | | unfold FO_V; clear - N10 HPL; lia];
              unfold in_app, kLowShadowBeg, kHighMemBeg in N11; unfold FO_V; clear - N11 HPL; lia |];
            split;
            [ apply (range_addressable_sub _ _ (x_fr cx + 32) 20); [exact (s23l_v_addr _ _ HF8 HZST) | unfold FO_V; lia
              | unfold FO_V; lia] |];
            intros _; unfold FO_V;
            apply (s23l_hull_v _ (x_fr cx) (Z.of_nat (length par) + 1) N8 ltac:(lia) ltac:(lia));
            intros q Hq; pose proof (HZST (Z.to_nat q) ltac:(rewrite lt_fsh_len; lia)) as Hb;
            rewrite Z2Nat.id in Hb by lia; change (shadow_addr (x_fr cx)) with (x_sh cx); rewrite Hb; discriminate)
      ltac:(rewrite s23l_len_zb; intros a Ha; apply (aview_some_of_apresent SEGS);
            pose proof (Z.mod_pos_bound (mt + 20 * Z.of_nat j + Z.of_nat (length (fst e))) 8 ltac:(lia));
            apply (proj1 (HMpres a ltac:(lia))))
      ltac:(rewrite s23l_len_zb; intros a Ha; apply (aview_some_of_apresent SEGS);
            pose proof (Z.mod_pos_bound (x_fr cx + FO_V + Z.of_nat (length par)) 8 ltac:(lia));
            apply (proj1 (HFpres a ltac:(unfold FO_V in *; lia))))
      HROM). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ3 & HP3 & HQ3 & HK3).
  (* back at 0x85b00: the callee-saved registers, and every byte outside the window below s1 *)
  assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ s23_scr cx a -> rdW W mem2 a = rdW W mem0 a).
  { intros a Ha Hn. unfold s23_scr in Hn. rewrite HK3; [rewrite KT; exact (MK a Ha ltac:(unfold s23_scr; lia)) | exact Ha
      | lia | tauto]. }
  assert (H176c : rdword (rdW W mem2) (x_s1 cx + 176) = Some SHADOW_OFF).
  { apply (s23_kept_word (rdW W mem0)); [|exact H176]. intros x Hx. apply KC; [lia | unfold s23_scr; lia]. }
  assert (Q9 : getr regs2 9 = w64 (x_s1 cx))
    by (rewrite (s23l_pres _ _ 9%bv HP3) by s23l_cs; rewrite (TK 9%bv ltac:(s23l_in)); exact G9).
  (* the strcmp answer: a0 = 0 exactly when the two parents are equal *)
  assert (HQ : (bv_unsigned (getr regs2 10) <? 1) = (SegModel.strcmp (fst e) par =? 0)).
  { pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    destruct (SegModel.strcmp (fst e) par =? 0) eqn:Hs.
    - apply (s23_strcmp0 _ _ EN0 (proj2 HPv)) in Hs. apply Z.ltb_lt.
      assert (Hz : getr regs2 10 = w64 0) by (apply HQ3; f_equal; exact Hs).
      rewrite Hz. unfold w64. rewrite unsigned_lit_small by lia. lia.
    - apply Z.ltb_ge. destruct (Z.eq_dec (bv_unsigned (getr regs2 10)) 0) as [H0|H0]; [|lia].
      exfalso. assert (Hz : getr regs2 10 = w64 0).
      { apply bv_eq. rewrite H0. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
      apply HQ3 in Hz. assert (Hp : fst e = par) by (rewrite <- Hzsx, <- Hzsy, Hz; reflexivity).
      apply (s23_strcmp0 _ _ EN0 (proj2 HPv)) in Hp. rewrite Hp in Hs. discriminate Hs. }
  pose proof (s23l_seedC W regs2 mem2 (x_s1 cx) Q9 ltac:(lia) ltac:(lia) H176c) as HSC.
  remember (s23_E regs2 []) as E2 eqn:HE2.
  assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply s23_E_img).
  (* 0x85b00 .. 0x85b20: a5 := 176(s1), a0 := seqz a0, s8 |= a0, s5 -= 1, s4 += 20, s3 += 20; stops at beqz s5 *)
  paj_run_sh RUNP HSC HJ3.
  { awr_ok_tac. }
  s23l_nm HSC msP mdP. pose proof (s23_ro_kept SEGS _ _ _ _ _ HFr eq_refl) as K4. clear HF HFr HG.
  psrr_branch_pi RUNP BR HSC.
  + (* s5 = 0: the scan is done, to 0x85b38 *)
    rewrite branch_eq_U in Hc0.
    rewrite (U_atom_off _ 21 (Z.of_nat (length t) - Z.of_nat j) (-1)) in Hc0
      by (first [lia | rewrite HE2, (s23_E_reg _ _ 21 21%bv eq_refl), (s23l_pres _ _ 21%bv HP3) by s23l_cs;
                       rewrite (TK 21%bv ltac:(s23l_in)); exact R21]).
    rewrite U_lit in Hc0 by lia. apply Z.eqb_eq in Hc0.
    paj_run_to_sh RUNTOP HSC HJ3 0xe04.
    { awr_ok_tac. }
    s23l_nm HSC msF mdF. pose proof (s23_ro_kept SEGS _ _ _ _ _ HFr eq_refl) as K5. clear HF HFr HG.
    pmkst HSC.
    apply (HX38 cx ly S W regs0 mem0 md0 k acc c m tab mt par vid (ms_regs msF) (ms_mem msF) mdF CTX).
    * split; [exact HJ3|]. split.
      -- intros r Hr. unfold S23_RLK in Hr. cbn [In] in Hr.
         repeat (destruct Hr as [<- | Hr];
           [first [s23l_kregC HSC HE2 HP3 TK RK
                  | let P := fresh "P" in s23_prraw HSC (15%bv : bv 5) P; rewrite P, R15; reflexivity] |]).
         destruct Hr.
      -- intros a Ha Hn. rewrite K5, K4. exact (KC a Ha Hn).
    * change (snd (x_decl cx i)) with t.
      replace (existsb (s23_dup par vid) t) with (existsb (s23_dup par vid) (firstn (Datatypes.S j) t))
        by (rewrite firstn_all2 by lia; reflexivity).
      rewrite HEX.
      s23_vreg HSC (24%bv : bv 5).
      rewrite U_SAlu, U_SAlu, U_lit by lia.
      rewrite (U_atom _ 24 (seg_spec.b2z (existsb (s23_dup par vid) (firstn j t))))
        by (first [apply s23l_b2z_rng | rewrite HE2, (s23_E_reg _ _ 24 24%bv eq_refl), (s23l_pres _ _ 24%bv HP3) by s23l_cs;
                   rewrite (TK 24%bv ltac:(s23l_in)); exact R24]).
      rewrite U_SOff, HE2, (s23_E_reg _ _ 10 10%bv eq_refl), Z.add_0_r.
      rewrite (zcanon_small (bv_unsigned (getr regs2 10))) by (pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as Hr;
        change (bv_modulus 64) with (2 ^ 64) in Hr; lia).
      cbn [zalu_raw]. rewrite HQ.
      change (if SegModel.strcmp (fst e) par =? 0 then 1 else 0) with (seg_spec.b2z (SegModel.strcmp (fst e) par =? 0)).
      rewrite (zcanon_small (seg_spec.b2z (SegModel.strcmp (fst e) par =? 0))) by apply s23l_b2z_rng.
      apply s23l_or_b2z.
  + (* s5 <> 0: the next entry, back to 0x85ad8 *)
    rewrite branch_eq_U in Hc0.
    rewrite (U_atom_off _ 21 (Z.of_nat (length t) - Z.of_nat j) (-1)) in Hc0
      by (first [lia | rewrite HE2, (s23_E_reg _ _ 21 21%bv eq_refl), (s23l_pres _ _ 21%bv HP3) by s23l_cs;
                       rewrite (TK 21%bv ltac:(s23l_in)); exact R21]).
    rewrite U_lit in Hc0 by lia. apply Z.eqb_neq in Hc0.
    paj_run_to_sh RUNTOP HSC HJ3 0xda4.
    { awr_ok_tac. }
    s23l_nm HSC msF mdF. pose proof (s23_ro_kept SEGS _ _ _ _ _ HFr eq_refl) as K5. clear HF HFr HG.
    pmkst HSC.
    apply (HLS cx ly S W regs0 mem0 md0 k acc c m tab mt par vid (ms_regs msF) (ms_mem msF) mdF CTX).
    * split; [exact HJ3|]. split.
      -- intros r Hr. unfold S23_RLK in Hr. cbn [In] in Hr.
         repeat (destruct Hr as [<- | Hr];
           [first [s23l_kregC HSC HE2 HP3 TK RK
                  | let P := fresh "P" in s23_prraw HSC (15%bv : bv 5) P; rewrite P, R15; reflexivity] |]).
         destruct Hr.
      -- intros a Ha Hn. rewrite K5, K4. exact (KC a Ha Hn).
    * change (snd (x_decl cx i)) with t. lia.
    * s23_vreg HSC (19%bv : bv 5).
      rewrite (U_atom_off _ 19 (mt + 16 + 20 * Z.of_nat j) 20)
        by (first [lia | rewrite HE2, (s23_E_reg _ _ 19 19%bv eq_refl), (s23l_pres _ _ 19%bv HP3) by s23l_cs;
                         rewrite (TK 19%bv ltac:(s23l_in)); exact R19]).
      lia.
    * s23_vreg HSC (20%bv : bv 5).
      rewrite (U_atom_off _ 20 (mt + 20 * Z.of_nat j) 20)
        by (first [lia | rewrite HE2, (s23_E_reg _ _ 20 20%bv eq_refl), (s23l_pres _ _ 20%bv HP3) by s23l_cs;
                         rewrite (TK 20%bv ltac:(s23l_in)); exact R20]).
      lia.
    * change (snd (x_decl cx i)) with t. s23_vreg HSC (21%bv : bv 5).
      rewrite (U_atom_off _ 21 (Z.of_nat (length t) - Z.of_nat j) (-1))
        by (first [lia | rewrite HE2, (s23_E_reg _ _ 21 21%bv eq_refl), (s23l_pres _ _ 21%bv HP3) by s23l_cs;
                         rewrite (TK 21%bv ltac:(s23l_in)); exact R21]).
      lia.
    * change (snd (x_decl cx i)) with t. rewrite HEX.
      s23_vreg HSC (24%bv : bv 5).
      rewrite U_SAlu, U_SAlu, U_lit by lia.
      rewrite (U_atom _ 24 (seg_spec.b2z (existsb (s23_dup par vid) (firstn j t))))
        by (first [apply s23l_b2z_rng | rewrite HE2, (s23_E_reg _ _ 24 24%bv eq_refl), (s23l_pres _ _ 24%bv HP3) by s23l_cs;
                   rewrite (TK 24%bv ltac:(s23l_in)); exact R24]).
      rewrite U_SOff, HE2, (s23_E_reg _ _ 10 10%bv eq_refl), Z.add_0_r.
      rewrite (zcanon_small (bv_unsigned (getr regs2 10))) by (pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as Hr;
        change (bv_modulus 64) with (2 ^ 64) in Hr; lia).
      cbn [zalu_raw]. rewrite HQ.
      change (if SegModel.strcmp (fst e) par =? 0 then 1 else 0) with (seg_spec.b2z (SegModel.strcmp (fst e) par =? 0)).
      rewrite (zcanon_small (seg_spec.b2z (SegModel.strcmp (fst e) par =? 0))) by apply s23l_b2z_rng.
      apply s23l_or_b2z.
Qed.

(* ===== piece m ===== *)
(* ---- piece m: S15_X40 (0x85b40) to the join S15_PJ (0x85b7c) through the checked memcpy of v into mt[mn],
   or, the table full, through the -1 exit 0x85d44 .. 0x85d68 (v out of scope: the frame's shadow bytes 4 .. 6
   become 0xf8) to K85bd0 ---- *)

(* a word read back from a symbolic state's chunk (LLVMFuzzerTestOneInput_s10k.v:95-102, _s10, copied) *)
Lemma s23m_rd_chunk8 : forall E H mem base off a e v cs,
  Forall (YP09.chunk_ok SEGS E (mrestrict H mem) base) cs -> In (YP09.mkChunk off (CVal 8 e)) cs ->
  a = base + off -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H mem) a = Some v.
Proof.
intros E H mem base off a e v cs Hc Hin -> He Hv. rewrite Forall_forall in Hc. specialize (Hc _ Hin).
apply rdword_of_val_mem; [|exact Hv].
apply (val_of_chunk_ok SEGS E _ base off 8 e v Hc He); [exact Hv | cbn; lia].
Qed.

(* a callee-saved register across a call (s15a.v:103-108, copied) *)
Lemma s23m_pres : forall (regs2 regs3 : bvmap 5 word) (r : bv 5),
  aregs_preserved regs2 regs3 -> acallee_saved (bv_unsigned r) -> getr regs3 r = getr regs2 r.
Proof.
intros regs2 regs3 r HP Hz. pose proof (HP (bv_unsigned r) Hz) as H.
rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.

(* a callee-saved register across a call, by its number (LLVMFuzzerTestOneInput_s22e.v:80-82, copied) *)
Lemma s23m_pres' : forall regs regs' (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz <-. exact (HP z Hz). Qed.
(* a register as a plain run's state at a call names it *)
Ltac s23m_prok HS r P :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as P;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in P;
    cbn [ms_regs restrict mkst] in P
  end.

(* the model: the counter of m_decl_go is its start plus the entries it added *)
Lemma s23m_decl_len : forall l tab cap a, 0 <= a -> 0 <= fst (SegModel.m_decl_go l tab cap a) ->
  fst (SegModel.m_decl_go l tab cap a) + Z.of_nat (length tab) =
  a + Z.of_nat (length (snd (SegModel.m_decl_go l tab cap a))).
Proof.
induction l as [|g l IH]; intros tab cap a Ha; cbn [SegModel.m_decl_go]; [cbn; lia|].
destruct (SegModel.ms_ignore g); [apply IH; exact Ha|].
destruct (SegModel.m_split (SegModel.ms_name g)) as [[p v]|]; [|apply IH; exact Ha].
destruct (existsb _ tab); [apply IH; exact Ha|].
destruct (cap <=? Z.of_nat (length tab)); [cbn; lia|].
intros Hf. pose proof (IH (tab ++ [(p, v)]) cap (a + 1) ltac:(lia) Hf) as H.
rewrite length_app in H. cbn [length] in H. lia.
Qed.

(* the addiw of a small value *)
Lemma s23m_U_addw1 : forall E e v, U E e = v -> 0 <= v < 2 ^ 31 - 1 -> U E (SAluw ALU_ADD e (SLit 1)) = v + 1.
Proof.
intros E e v He Hv. rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite He, U_lit by lia.
rewrite (Z.mod_small v) by lia. change (1 mod 2 ^ 32) with 1. rewrite swrap32_id by lia.
apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

(* bytes read through two readers that agree on a window *)
Lemma s23m_zs_xfer : forall (rd rd' : reader) a a' l n,
  (forall k, 0 <= k < n -> rd' (a' + k) = rd (a + k)) -> Z.of_nat (length l) <= n -> sa_zs rd a l -> sa_zs rd' a' l.
Proof. intros rd rd' a a' l n HK Hl H j Hj. rewrite HK by lia. exact (H j Hj). Qed.
Lemma s23m_val_xfer : forall (rd rd' : reader) a a' n v w,
  (forall k, 0 <= k < w -> rd' (a' + k) = rd (a + k)) -> Z.of_nat n <= w -> sa_val rd a n v -> sa_val rd' a' n v.
Proof. intros rd rd' a a' n v w HK Hl H j Hj. rewrite HK by lia. exact (H j Hj). Qed.

(* the seed after the call (0x85b68): 104(s1) the entries added (atom 32), 176(s1) the shadow base (atom 33); the
   two counter slots 104(s1) and 120(s1) are write windows *)
Definition s23m_rA : YP09.region := YP09.mkRegion (Some 9%nat) 104 112 104 112 [YP09.mkChunk 104 (CVal 8 (SOff 32 0))].
Definition s23m_rB : YP09.region := YP09.mkRegion (Some 9%nat) 120 128 120 128 [].
Definition s23m_rC : YP09.region := YP09.mkRegion (Some 9%nat) 176 184 0 0 [YP09.mkChunk 176 (CVal 8 (SOff 33 0))].
Lemma s23m_seedP : forall (W : world SEGS) regs mem s1 a,
  getr regs 9 = w64 s1 -> 0 <= s1 -> s1 + 192 <= 2 ^ 64 -> 0 <= a < 2 ^ 64 ->
  rdword (rdW W mem) (s1 + 104) = Some a -> rdword (rdW W mem) (s1 + 176) = Some SHADOW_OFF ->
  (forall o, (104 <= o < 112 \/ 120 <= o < 128) -> writable_at SEGS (mrestrict (w_H W) mem) (s1 + o)) ->
  st_ok_pi SEGS VAL (s23_E regs [a; SHADOW_OFF]) (mkSS 0xe34 sr_atoms [s23m_rA; s23m_rB; s23m_rC] None (mkFacts [] [] []))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0xe34)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s1 a R9 Hs0 Hs1 Ha H104 H176 Hwr.
assert (U9 : bv_unsigned (ew (s23_E regs [a; SHADOW_OFF]) 9) = s1)
  by (rewrite (s23_E_reg _ _ 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (E32 : ew (s23_E regs [a; SHADOW_OFF]) 32 = Z_to_bv 64 a)
  by (exact (s23_E_val regs [a; SHADOW_OFF] 0 ltac:(unfold A_TEXT; lia))).
assert (E33 : ew (s23_E regs [a; SHADOW_OFF]) 33 = Z_to_bv 64 SHADOW_OFF)
  by (exact (s23_E_val regs [a; SHADOW_OFF] 1 ltac:(unfold A_TEXT; lia))).
set (E := s23_E regs [a; SHADOW_OFF]) in *.
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. unfold s23_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  + unfold region_ok, s23m_rA.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hwr; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ s1 104 8 (SOff 32 0) a);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    exact (val_mem_of_rdword SEGS (w_H W) mem _ a H104).
  + unfold region_ok, s23m_rB.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hwr; lia | apply Forall_nil].
  + unfold region_ok, s23m_rC.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ s1 176 8 (SOff 33 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; cbn; lia | cbn; lia |].
    exact (val_mem_of_rdword SEGS (w_H W) mem _ _ H176).
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, s23m_rA, s23m_rB, s23m_rC.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9. repeat split; lia.
- split; [exact I | split; [exact I | exact I]].
Qed.

Ltac s23m_in := cbn [In]; solve [repeat (first [left; reflexivity | right])].

Lemma s23m_x40 : S15_PJ B MT i -> S15_X40 B MT i.
Proof.
intros HPJ. unfold S15_X40.
intros cx ly S W regs0 mem0 md0 k acc c m tab mt par vid regs mem md CTX REL Hex R21.
destruct (s23_ctx_num B MT i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX)
  as (HAR0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & Bc & Bm & Btab & Bmt).
pose proof (s23_ctx_slots B MT i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX) as HSL0.
pose proof CTX as (HB & HF0 & Hi & HC & Hcb & Hmb & Htb & Hmtb & Hig & Hsp & R15 & R18 & R22 & R23 & R25 & R26
  & R27 & Ha0 & HSL & Hcm & Htabs & Hv & Hvid).
pose proof HC as (HFR & HIMG & HBLK & HBUD).
pose proof HFR as (HJ0 & G2 & G3 & G4 & G8 & G9 & HSV & HH0 & HH8 & HH16 & HFW & H176 & HZS).
destruct (s23_layout B MT LAWS cx ly S W regs0 mem0 md0 k LFO_NV HB HFR) as (Lsp16 & _).
destruct REL as (HJ & RK & KR).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HB as (HPRE & _). pose proof HPRE as (_ & _ & _ & Hgp0 & Htp0 & _).
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
assert (HFin : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite N6; left; reflexivity).
pose proof Bmt as (Imt & Mt4 & _ & Mtc & Mta).
unfold x_mtn, seg_spec.MVLAN_SIZE in Mtc, Mta.
pose proof Btab as (_ & T4 & _ & Tc & _). pose proof Bm as (_ & M4 & _ & Mc & _).
unfold x_tabn, seg_spec.RVLAN_SIZE, seg_spec.SEG_M_SIZE in Tc, Mc.
pose proof (HSL 104 (fst (x_decl cx i)) ltac:(apply in_or_app; right; cbn [In]; right; right; left; reflexivity))
  as H104.
pose proof (s23_rdword_range _ _ _ _ _ H104) as Ra0.
(* the model's numbers *)
set (t := snd (x_decl cx i)) in *. set (a := fst (x_decl cx i)) in *.
assert (Hal : a + Z.of_nat (length (x_tab0 cx)) = Z.of_nat (length t)).
{ pose proof (s23m_decl_len (firstn i (SegModel.mc_seg (x_mcF cx))) (x_tab0 cx) (x_cap cx) 0 ltac:(lia) Ha0) as Hq.
  exact Hq. }
assert (Hsh : 0 <= x_sh cx < 2 ^ 64)
  by (unfold x_sh, shadow_addr, SHADOW_OFF; pose proof (Z.div_pos (x_fr cx) 8); pose proof (Z.div_le_upper_bound (x_fr cx) 8 (2 ^ 50)); lia).
pose proof (Z.div_mod (x_fr cx) 64 ltac:(lia)) as Hq. rewrite N8, Z.add_0_r in Hq. set (q := x_fr cx / 64) in Hq.
assert (Ush : x_sh cx = SHADOW_OFF + 8 * q).
{ unfold x_sh, shadow_addr. rewrite Hq. f_equal. replace (64 * q) with (q * 8 * 8) by lia. rewrite Z.div_mul by lia. lia. }
assert (HF8 : x_fr cx mod 8 = 0) by (rewrite Hq; rewrite Z.mul_comm; replace (q * 64) with ((q * 8) * 8) by lia; apply Z_mod_mult).
(* the registers and the slots at 0x85b40 *)
assert (R9 : getr regs 9 = w64 (x_s1 cx)) by (rewrite (RK 9%bv ltac:(unfold S23_RLK; s23m_in)); exact G9).
assert (R15' : getr regs 15 = w64 SHADOW_OFF) by (rewrite (RK 15%bv ltac:(unfold S23_RLK; s23m_in)); exact R15).
assert (HSLX : lt_slots cx (rdW W mem) (s23_slots cx tab mt a (Z.of_nat (length t)) m)).
{ intros o v Hin. assert (Ho : 32 <= o <= 184).
  { unfold s23_slots in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- _; lia|]). destruct Hin. }
  apply (s23_kept_word (rdW W mem0)); [|exact (HSL0 o v Hin)].
  intros x Hx. apply KR; [lia | unfold s23_scr; lia]. }
set (vals := s23_vals cx tab mt a (Z.of_nat (length t)) m ++ []).
set (G := mkFacts [(9%nat, mkAF 0x7fff7f800000 (2 ^ 47) 0); (15%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
  (37%nat, mkAF 0 39 0)] [] []).
assert (HGOK : forall rr, getr rr 9 = w64 (x_s1 cx) -> getr rr 15 = w64 SHADOW_OFF -> facts_ok (s23_E rr vals) G).
{ intros rr Q9 Q15.
  assert (V9 : bv_unsigned (ew (s23_E rr vals) 9) = x_s1 cx)
    by (rewrite (s23_E_reg _ _ 9 9%bv eq_refl), Q9; apply unsigned_lit_small; lia).
  assert (V15 : bv_unsigned (ew (s23_E rr vals) 15) = SHADOW_OFF)
    by (rewrite (s23_E_reg _ _ 15 15%bv eq_refl), Q15; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (E37 : ew (s23_E rr vals) 37 = Z_to_bv 64 (Z.of_nat (length t)))
    by (exact (s23_E_val rr vals 5 ltac:(unfold A_TEXT; lia))).
  assert (V37 : bv_unsigned (ew (s23_E rr vals) 37) = Z.of_nat (length t))
    by (rewrite E37; apply unsigned_lit_small; lia).
  split; [|split; exact I]. cbn [G f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite V9, V15, V37. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold SHADOW_OFF.
  repeat split; first [exact I | lia]. }
pose proof (s23_s1_seed 0xe0c 0 0 cx W regs mem tab mt a (Z.of_nat (length t)) m [] G
  HSLX R9 R15' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold FO_V; lia) ltac:(lia) ltac:(lia) Ra0 ltac:(lia) Hsh
  ltac:(lia) ltac:(intros o Ho; lia) eq_refl (HGOK regs R9 R15')) as HS.
fold vals in HS.
assert (HAE : env_agree 32 (Ereg regs (map (Z_to_bv 64) vals)) (s23_E regs vals)) by apply s23_E_agree.
remember (s23_E regs vals) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply s23_E_img).
assert (U21 : U E (SOff 21 0) = Z.of_nat (length t))
  by (apply U_atom; [rewrite HE, (s23_E_reg _ _ 21 21%bv eq_refl); exact R21 | lia]).
assert (U32 : U E (SOff 32 0) = x_cap cx)
  by (apply U_atom; [rewrite HE; exact (s23_E_val regs vals 0 ltac:(unfold A_TEXT; lia)) | lia]).
unfold cfg_at, w64.
(* 0x85b40: a0 := cap, then bge s5,a0 *)
paj_run_sh RUNP HS HJ.
{ awr_ok_tac. }
pose proof (s23_ro_kept SEGS _ _ _ _ _ HFr eq_refl) as K1. clear HF HFr HG.
rename ms into msA.
psrr_branch_pi RUNP BR HS.
- (* mn = cap: the table is full *)
  rewrite s23_br_ge, U21, U32 in Hc by (rewrite ?U21, ?U32; lia). apply Z.leb_le in Hc.
  (* the model: turn i finds the table full, m_declared answers -1 with the table t *)
  assert (HD : x_decl cx (Datatypes.S i) = (-1, t)).
  { unfold x_decl. rewrite (s23_decl_step _ _ _ i par vid Hi Hig Hsp Ha0). cbv zeta.
    change (SegModel.m_decl_go (firstn i (SegModel.mc_seg (x_mcF cx))) (x_tab0 cx) (x_cap cx) 0) with (x_decl cx i).
    fold t. rewrite Hex. replace (x_cap cx <=? Z.of_nat (length t)) with true by (symmetry; apply Z.leb_le; lia).
    reflexivity. }
  assert (HMD : SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx) = (-1, t)).
  { unfold SegModel.m_declared. rewrite (s23_decl_full (SegModel.mc_seg (x_mcF cx)) (x_tab0 cx) (x_cap cx) (Datatypes.S i) ltac:(lia)).
    - change (SegModel.m_decl_go (firstn (Datatypes.S i) (SegModel.mc_seg (x_mcF cx))) (x_tab0 cx) (x_cap cx) 0)
        with (x_decl cx (Datatypes.S i)). exact HD.
    - change (SegModel.m_decl_go (firstn (Datatypes.S i) (SegModel.mc_seg (x_mcF cx))) (x_tab0 cx) (x_cap cx) 0)
        with (x_decl cx (Datatypes.S i)). rewrite HD. cbn. lia. }
  (* 0x85b44 -> 0x85d44 *)
  paj_run_to_sh RUNTOP HS HJ 0x1010.
  { awr_ok_tac. }
  pose proof (s23_ro_kept SEGS _ _ _ _ _ HFr eq_refl) as K2. clear HF HFr HG.
  s23_mdv. pmkst HS. rename ms into ms1, mdv into md1.
  assert (Q : forall r : bv 5, In r [2; 3; 4; 8; 9; 15]%bv -> getr (ms_regs ms1) r = getr regs0 r).
  { intros r Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [lazymatch goal with |- getr _ ?r = getr _ ?r =>
      rewrite <- (RK r ltac:(unfold S23_RLK; s23m_in)) end; s23_kreg_goal HS HE|]).
    destruct Hr. }
  assert (Q9 : getr (ms_regs ms1) 9 = w64 (x_s1 cx)) by (rewrite (Q 9%bv ltac:(s23m_in)); exact G9).
  assert (Q15 : getr (ms_regs ms1) 15 = w64 SHADOW_OFF) by (rewrite (Q 15%bv ltac:(s23m_in)); exact R15).
  pose proof (proj1 HJ) as HAR1.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTKP1 & _).
  destruct (al_frames _ _ LAWS ly S W (ms_mem ms1) md1 LT_FCLS (x_fpos cx) HAR1 HFin) as (_ & _ & _ & HFSp1).
  rewrite N7 in HFSp1. change (fs_frame_bytes LT_FCLS / 8) with 64 in HFSp1.
  assert (HSL1 : lt_slots cx (rdW W (ms_mem ms1)) (s23_slots cx tab mt a (Z.of_nat (length t)) m)).
  { intros o v Hin. apply (s23_kept_word (rdW W mem)); [|exact (HSLX o v Hin)].
    intros x _. rewrite K2. apply K1. }
  clear HS.
  (* the seed at 0x85d44: the s1 slots with 104(s1) a write window, and the frame's shadow (base SH(FR), atom 38)
     with its bytes 4 .. 6 a write window *)
  pose proof (s23_s1_seed 0x1010 104 112 cx W (ms_regs ms1) (ms_mem ms1) tab mt a (Z.of_nat (length t)) m [] G
    HSL1 Q9 Q15 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold FO_V; lia) ltac:(lia) ltac:(lia) Ra0 ltac:(lia) Hsh
    ltac:(lia) ltac:(intros o Ho; apply (apresent_writable SEGS); apply HSTKP1; rewrite HSTK; lia) eq_refl
    (HGOK (ms_regs ms1) Q9 Q15)) as HS0.
  fold vals in HS0.
  assert (HAE1 : env_agree 32 (Ereg (ms_regs ms1) (map (Z_to_bv 64) vals)) (s23_E (ms_regs ms1) vals))
    by apply s23_E_agree.
  assert (F9 : bv_unsigned (ew (s23_E (ms_regs ms1) vals) 9) = x_s1 cx)
    by (rewrite (s23_E_reg _ _ 9 9%bv eq_refl), Q9; apply unsigned_lit_small; lia).
  assert (F38 : bv_unsigned (ew (s23_E (ms_regs ms1) vals) 38) = x_sh cx).
  { assert (E38 : ew (s23_E (ms_regs ms1) vals) 38 = Z_to_bv 64 (x_sh cx))
      by (exact (s23_E_val (ms_regs ms1) vals 6 ltac:(unfold A_TEXT; lia))).
    rewrite E38. apply unsigned_lit_small. exact Hsh. }
  pose proof (st_ok_pi_add_region _ _ _ (fshadow_region 38 LT_FCLS 4 7 []) HS0 eq_refl) as HSF.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSF.
  assert (HSFr : st_ok_pi SEGS VAL (s23_E (ms_regs ms1) vals)
      (mkSS 0x1010 sr_atoms [fshadow_region 38 LT_FCLS 4 7 []; s1_region 104 112] None G)
      (restrict (w_H W) (mkst (ms_regs ms1) (Z_to_bv 64 (BASE + 0x1010)) (ms_mem ms1) (seg_rom SEGS)))).
  { apply HSF.
    - rewrite restrict_mkst_fx. cbn [ms_mem]. unfold region_ok, fshadow_region.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      change (fs_frame_bytes LT_FCLS / 8) with 64. rewrite F38.
      split; [lia|]. split; [rewrite Ush; unfold SHADOW_OFF; lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFSp1 o ltac:(lia))).
    - cbn [all_disjoint]. split; [|exact I]. unfold extent_disjoint, fshadow_region, s1_region.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. change (fs_frame_bytes LT_FCLS / 8) with 64.
      rewrite F38, F9. left. rewrite Ush. unfold SHADOW_OFF. lia. }
  clear HSF HS0.
  remember (s23_E (ms_regs ms1) vals) as EF eqn:HEF.
  assert (HEIF : img_env VAL A_LIM EF) by (rewrite HEF; apply s23_E_img).
  (* 0x85d44 .. 0x85d68: v's three shadow bytes 0xf8, 104(s1) := -1, a6 := m, s8 := tab, j 0x85bd0 *)
  paj_run_to_sh RUNTOP HSFr HJ 0xe9c.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
    eapply awr_ok_cons_gen with (n := 38%nat) (b := x_sh cx); [reflexivity | exact F38 | |].
    { intros a' Ha'. cbn [YP09.r_wlo YP09.r_whi] in Ha'.
      right; right; right; left. exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|].
      right. rewrite N7. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes LT_FCLS / 8) with 64.
      unfold x_sh in Ha'. lia. }
    eapply awr_ok_cons_stack_off with (n := 9%nat) (d := x_s1 cx - x_sp0 cx);
      [reflexivity | rewrite F9; lia | cbn [YP09.r_wlo]; rewrite HSTK; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
  rename HF into HFF, HFr into HFrF, HG into HGF.
  s23_mdv. rename ms into msF, mdv into mdF.
  (* the run wrote only v's three shadow bytes and 104(s1) *)
  assert (KF : forall a', 0 <= a' < 2 ^ 64 -> ~ (x_sh cx + 4 <= a' < x_sh cx + 7) ->
    ~ (x_s1 cx + 104 <= a' < x_s1 cx + 112) -> rdW W (ms_mem msF) a' = rdW W (ms_mem ms1) a').
  { intros a' Ha' N1' N2'.
    apply (kept_of_frame EF _ (w_H W) (ms_mem ms1) (ms_mem msF)
      (fun x => (x_sh cx + 4 <= x < x_sh cx + 7) \/ (x_s1 cx + 104 <= x < x_s1 cx + 112)) HFrF);
      [| exact Ha' | intros [Hq' | Hq']; contradiction].
    intros b wlo whi x Hin Hx.
    lazymatch type of Hin with In _ (windows ?rs) => let w := eval vm_compute in (windows rs) in
      change (In (b, wlo, whi) w) in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [Hq' | Hin]; [injection Hq' as <- <- <-; cbn [base_val] in Hx; rewrite ?F38, ?F9 in Hx;
      cbv beta; lia |]).
    destruct Hin. }
  (* the three shadow bytes and 104(s1), read back from the run's chunks *)
  lazymatch type of HSFr with st_ok_pi _ _ _ ?ssx _ =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
    let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
    pose proof (PaLibG.st_ok_pi_region_nth EF ssx (restrict (w_H W) msF) 0%nat r0 HSFr ltac:(vm_compute; reflexivity)) as RF0;
    pose proof (PaLibG.st_ok_pi_region_nth EF ssx (restrict (w_H W) msF) 1%nat r1 HSFr ltac:(vm_compute; reflexivity)) as RF1
  end.
  destruct RF0 as (_ & _ & _ & CF0). destruct RF1 as (_ & _ & _ & CF1).
  cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in CF0, CF1. rewrite F38 in CF0. rewrite F9 in CF1.
  assert (HZ3 : sa_zs (rdW W (ms_mem msF)) (x_sh cx + 4) [248; 248; 248])
    by exact (s23j_zs_ok SEGS EF (w_H W) (ms_mem msF) (x_sh cx) _ [248; 248; 248] 4 CF0 ltac:(vm_compute; reflexivity)).
  assert (H104F : rdword (rdW W (ms_mem msF)) (x_s1 cx + 104) = Some 18446744073709551615).
  { apply (s23m_rd_chunk8 EF (w_H W) (ms_mem msF) (x_s1 cx) 104 _ (SLit 18446744073709551615) _ _ CF1);
      [s23m_in | reflexivity | reflexivity | lia]. }
  (* the registers at 0x85bd0 *)
  assert (QF : forall r : bv 5, In r [2; 3; 4; 8; 9]%bv -> getr (ms_regs msF) r = getr regs0 r).
  { intros r Hr. rewrite <- (Q r ltac:(cbn [In] in Hr |- *; tauto)). cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [s23_kreg_goal HSFr HEF|]). destruct Hr. }
  assert (FR16 : getr (ms_regs msF) 16 = w64 m).
  { s23_vreg HSFr (16%bv : bv 5). apply U_atom; [rewrite HEF; exact (s23_E_val (ms_regs ms1) vals 7 ltac:(unfold A_TEXT; lia)) | lia]. }
  assert (FR21 : getr (ms_regs msF) 21 = w64 (x_sh cx)).
  { s23_vreg HSFr (21%bv : bv 5). apply U_atom; [rewrite HEF; exact (s23_E_val (ms_regs ms1) vals 6 ltac:(unfold A_TEXT; lia)) | lia]. }
  assert (FR24 : getr (ms_regs msF) 24 = w64 tab).
  { s23_vreg HSFr (24%bv : bv 5). apply U_atom; [rewrite HEF; exact (s23_E_val (ms_regs ms1) vals 2 ltac:(unfold A_TEXT; lia)) | lia]. }
  pmkst HSFr.
  (* every byte outside s23_D0 and v's three shadow bytes is the K85ac4 state's *)
  assert (KALL : forall a', 0 <= a' < 2 ^ 64 -> ~ s23_D0 cx mt (length t) a' -> ~ (x_sh cx + 4 <= a' < x_sh cx + 7) ->
    rdW W (ms_mem msF) a' = rdW W mem0 a').
  { intros a' Ha' HD0 Hsh'. unfold s23_D0 in HD0.
    rewrite KF by (first [exact Ha' | exact Hsh' | intros Hq'; apply HD0; tauto]).
    rewrite K2, K1. apply KR; [exact Ha' | intros Hq'; apply HD0; tauto]. }
  assert (Hf8 : forall j, 4 <= j < 7 -> rdW W (ms_mem msF) (x_sh cx + j) = Some 0xf8).
  { intros j Hj. replace (x_sh cx + j) with (x_sh cx + 4 + Z.of_nat (Z.to_nat (j - 4))) by lia.
    rewrite (HZ3 (Z.to_nat (j - 4)) ltac:(cbn [length]; lia)).
    assert (Hj3 : (Z.to_nat (j - 4) < 3)%nat) by lia.
    destruct (Z.to_nat (j - 4)) as [|[|[|?]]]; [reflexivity | reflexivity | reflexivity | lia]. }
  pose proof Htabs as (_ & _ & _ & _ & Hmtab0 & _).
  assert (HmtabF : sa_mtab (rdW W (ms_mem msF)) mt t).
  { apply (s23_kept_mtab (rdW W mem0)); [|exact Hmtab0].
    intros x Hx. apply KALL.
    - lia.
    - unfold s23_D0, s23_scr. change ESTACK with 4096.
      intros [Hq1|[Hq1|[Hq1|Hq1]]]; clear - Hx Hq1 N1 N3 N13 Mtc Mt4 C1 Hc; lia.
    - rewrite Ush. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in Mta, N11.
      rewrite Hq in N11. unfold SHADOW_OFF. clear - Hx Mta Mtc N11 N10 N13 Hq Mt4 C1. lia. }
  destruct (s23_end B MT i cx ly S W regs0 mem0 md0 k acc c m tab mt par vid (ms_regs msF) (ms_mem msF) mdF t CTX HJ
    (QF 2%bv ltac:(s23m_in)) (QF 3%bv ltac:(s23m_in)) (QF 4%bv ltac:(s23m_in)) (QF 8%bv ltac:(s23m_in))
    (QF 9%bv ltac:(s23m_in)) KALL Hf8 HmtabF N13)
    as (HCORE' & Hc' & Hm' & Htab' & Hmt' & Hcm' & Htabs' & HSL').
  pose proof (HSL0 120 (Z.of_nat (length t)) ltac:(unfold s23_slots; s23m_in)) as H120.
  assert (H120F : rdword (rdW W (ms_mem msF)) (x_s1 cx + 120) = Some (Z.of_nat (length t))).
  { apply (s23_kept_word (rdW W mem0)); [|exact H120]. intros x Hx.
    rewrite KF; [rewrite K2, K1; apply KR; [lia | unfold s23_scr; lia] | lia | | lia].
    rewrite Ush. unfold SHADOW_OFF. clear - Hx N1 N10 Hq C1. lia. }
  change (SRr SEGS W (cfg_at SEGS (BASE + LO_K85bd0) (ms_regs msF) (ms_mem msF) mdF) (lt_post B MT cx)).
  apply (HKB fx cx ly S W (ms_regs msF) (ms_mem msF) mdF k acc c m tab mt HB HF0 HCORE' Hc' Hm' Htab' Hmt'
    FR16 FR21 FR24); [rewrite HMD; cbn [fst snd] | exact Hcm' | rewrite HMD; exact Htabs'].
  intros o v Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hq'|Hin]; [injection Hq' as <- <-;
    first [ exact H104F | exact H120F
          | apply HSL'; unfold LT_LV; apply in_or_app; first [left; s23m_in | right; s23m_in] ] |]).
  destruct Hin.
- (* mn < cap: the copy of v into mt[mn] *)
  rewrite s23_br_ge, U21, U32 in Hc by (rewrite ?U21, ?U32; lia). apply Z.leb_gt in Hc.
  (* the model: the parent fits the 16-byte field, turn i adds (par, vid) *)
  assert (Hpl : (length par < 16)%nat).
  { pose proof Hcm as [_ Hmc]. destruct Hmc as (bs & _ & Henc). pose proof Henc as (_ & _ & Hsegs & _).
    destruct (Hsegs i Hi) as (_ & Hname & _). destruct Hname as (_ & Hs16 & _).
    assert (Hn16 : (length (SegModel.ms_name (x_seg cx i)) < 16)%nat) by exact Hs16.
    destruct (s23_split_props _ _ _ Hsp) as (_ & Hle & _). lia. }
  destruct (s23_split_props _ _ _ Hsp) as (Hvr & _ & _).
  assert (HD : x_decl cx (Datatypes.S i) = (a + 1, t ++ [(par, vid)])).
  { unfold x_decl. rewrite (s23_decl_step _ _ _ i par vid Hi Hig Hsp Ha0). cbv zeta.
    change (SegModel.m_decl_go (firstn i (SegModel.mc_seg (x_mcF cx))) (x_tab0 cx) (x_cap cx) 0) with (x_decl cx i).
    fold t a. rewrite Hex. replace (x_cap cx <=? Z.of_nat (length t)) with false by (symmetry; apply Z.leb_gt; lia).
    reflexivity. }
  assert (Hab : 0 <= a <= 39) by lia.
  assert (U35 : U E (SOff 35 0) = mt)
    by (apply U_atom; [rewrite HE; exact (s23_E_val regs vals 3 ltac:(unfold A_TEXT; lia)) | lia]).
  assert (U33 : U E (SOff 33 0) = x_fr cx + FO_V)
    by (apply U_atom; [rewrite HE; exact (s23_E_val regs vals 1 ltac:(unfold A_TEXT; lia)) | unfold FO_V; lia]).
  (* 0x85b48 .. 0x85b64: s2 := mn + 1, a0 := mt + 20 mn, a2 := 20, a1 := v, the jal of the runtime's memcpy *)
  paj_run_shc RUNP RUNC HS HJ.
  { awr_ok_tac. }
  pose proof (s23_ro_kept SEGS _ _ _ _ _ HFr eq_refl) as K3. clear HF HFr HG.
  s23_mdv. rename ms into msC, mdv into mdC.
  s23m_prok HS (1%bv : bv 5) P1. s23m_prok HS (10%bv : bv 5) P10. s23m_prok HS (11%bv : bv 5) P11.
  s23m_prok HS (12%bv : bv 5) P12. s23m_prok HS (18%bv : bv 5) P18.
  assert (T1 : getr (ms_regs msC) 1 = Z_to_bv 64 (BASE + 0xe34)) by (rewrite P1; exact (codeptr_val E 0xe34 HEI)).
  assert (T10 : getr (ms_regs msC) 10 = w64 (mt + 20 * Z.of_nat (length t))).
  { apply (s23_reg_U _ _ _ _ _ P10). rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw].
    rewrite U21, U35, (U_lit E 20) by lia. unfold zcanon, M64.
    rewrite (Z.mod_small (Z.of_nat (length t) * 20)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (T11 : getr (ms_regs msC) 11 = w64 (x_fr cx + FO_V)) by (apply (s23_reg_U _ _ _ _ _ P11); exact U33).
  assert (T12 : getr (ms_regs msC) 12 = w64 20) by (apply (s23_reg_U _ _ _ _ _ P12); apply U_lit; lia).
  assert (T18 : getr (ms_regs msC) 18 = w64 (Z.of_nat (length t) + 1))
    by (apply (s23_reg_U _ _ _ _ _ P18); apply s23m_U_addw1; [exact U21 | lia]).
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regs (map (Z_to_bv 64) vals) [2; 3; 4; 8; 9; 22; 23; 25; 26; 27]%bv
    HS HAE ltac:(vm_compute; reflexivity)) as PKC.
  cbn [ms_regs restrict] in PKC.
  assert (RR : forall r, In r [2; 3; 4; 8; 9; 22; 23; 25; 26; 27]%bv -> getr (ms_regs msC) r = getr regs0 r).
  { intros r Hr. rewrite (PKC r Hr). apply RK. unfold S23_RLK. cbn [In] in Hr |- *. tauto. }
  pmkst HS.
  assert (HspT : spZ (ms_regs msC) = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
  { unfold spZ. rewrite (RR 2%bv ltac:(s23m_in)), G2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
  assert (P3' : getr (ms_regs msC) 3 = w64 (as_gp B)) by (rewrite (RR 3%bv ltac:(s23m_in)), G3; exact Hgp0).
  assert (P4' : getr (ms_regs msC) 4 = w64 (as_tp B)) by (rewrite (RR 4%bv ltac:(s23m_in)), G4; exact Htp0).
  assert (Ho16 : (x_s1 cx - x_sp0 cx) mod 16 = 0).
  { pose proof (Z.div_mod (x_s1 cx) 32 ltac:(lia)) as D1. rewrite N4 in D1.
    pose proof (Z.div_mod (x_sp0 cx) 16 ltac:(lia)) as D2. rewrite Lsp16 in D2.
    replace (x_s1 cx - x_sp0 cx) with ((2 * (x_s1 cx / 32) - x_sp0 cx / 16) * 16) by lia. apply Z_mod_mult. }
  assert (HraT : YK0s.ret_ok (Z_to_bv 64 (BASE + 0xe34))) by (apply ret_ok_codeptr_v; [lia | reflexivity]).
  (* the frame, the block mt and their facts at the jal *)
  pose proof (proj1 HJ) as HARC.
  destruct (al_frames _ _ LAWS ly S W (ms_mem msC) mdC LT_FCLS (x_fpos cx) HARC HFin) as (_ & _ & HFpC & HFSpC).
  rewrite N7 in HFpC, HFSpC. change (fs_frame_bytes LT_FCLS) with 512 in HFpC, HFSpC. change (512 / 8) with 64 in HFSpC.
  assert (KC0 : forall a', 0 <= a' < 2 ^ 64 -> ~ s23_scr cx a' -> rdW W (ms_mem msC) a' = rdW W mem0 a').
  { intros a' Ha' Hn. rewrite K3, K1. exact (KR a' Ha' Hn). }
  assert (ZSC : sa_zs (rdW W (ms_mem msC)) (shadow_addr (x_fr cx)) (lt_fsh LFO_NV)).
  { apply (s23_kept_zs (rdW W mem0)); [|exact HZS]. rewrite lt_fsh_len. change (Z.of_nat 36) with 36.
    intros x Hx. fold (x_sh cx) in Hx. rewrite Ush in Hx. unfold SHADOW_OFF in Hx.
    apply KC0; [clear - Hx N9 N10 Hq C1; lia|]. unfold s23_scr. change ESTACK with 4096.
    clear - Hx N1 N10 Hq C1. lia. }
  assert (RQ : req_size (x_mtn cx) = x_mtn cx).
  { unfold req_size. destruct (x_mtn cx =? 0) eqn:Eq0; [apply Z.eqb_eq in Eq0; unfold x_mtn, seg_spec.MVLAN_SIZE in Eq0; lia | reflexivity]. }
  pose proof (sep_block_frame SEGS B LAWS ly S W (ms_mem msC) mdC mt (x_mtn cx) LT_FCLS (x_fpos cx) HARC Imt HFin) as Dmf.
  unfold zdisjoint in Dmf. cbn [fst snd] in Dmf. rewrite N7, RQ in Dmf. change (fs_frame_bytes LT_FCLS) with 512 in Dmf.
  unfold x_mtn, seg_spec.MVLAN_SIZE in Dmf.
  pose proof (blk_off_imgP B ly S W (ms_mem msC) mdC mt (x_mtn cx) HARC Imt) as Omt.
  rewrite RQ in Omt. unfold off_img, x_mtn, seg_spec.MVLAN_SIZE in Omt.
  assert (HNI : ~ In (mt, x_mtn cx) (ablocks B (x_ly cx) (x_S cx))).
  { pose proof (Permutation_NoDup HBLK (s23_ablocks_NoDup B LAWS ly S W mem0 md0 HAR0)) as HND.
    cbn [app] in HND. inversion HND as [|? ? Hn _]. intros Hq'. apply Hn. right; right; right. exact Hq'. }
  assert (Hmt20 : mt + 20 * Z.of_nat (length t) + 20 <= mt + 20 * (x_cap cx + 1)) by lia.
  (* the checked memcpy: mt[mn] := v's 20 bytes *)
  eapply SRr_bind.
  { apply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIG SS___asan_memcpy) (AMEMCPY fx) W (ms_regs msC) (ms_mem msC)
      STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx)
      [(LT_FCLS, x_fpos cx)] ly S mdC k (mt + 20 * Z.of_nat (length t)) (x_fr cx + FO_V) 20 (x_s1 cx - x_sp0 cx)
      (Z_to_bv 64 (BASE + 0xe34)) HJ T10 T11 T12 ltac:(lia) ltac:(lia) ltac:(lia) HspT Ho16 ltac:(lia)
      ltac:(change ESTACK with 4096; rewrite HSTK; lia) P3' P4' T1 HraT).
    - intros a' Ha'. split.
      + right; right; left. exists mt, (x_mtn cx). split; [exact Imt|]. split; [exact HNI|].
        rewrite RQ. unfold x_mtn, seg_spec.MVLAN_SIZE. lia.
      + change ESTACK with 4096. lia.
    - intros a' Ha' _ [[_ Himg] | Hst]; exfalso.
      + pose proof (pa_img_range _ Himg) as HIR. unfold kImgEnd in HIR. lia.
      + lia.
    - exact (amem_range_of_block SEGS B LAWS ly S W (ms_mem msC) mdC mt (x_mtn cx) (mt + 20 * Z.of_nat (length t)) 20 HARC Imt ltac:(lia)
        ltac:(rewrite RQ; unfold x_mtn, seg_spec.MVLAN_SIZE; lia)).
    - exact (range_addressable_of_block SEGS B LAWS ly S W (ms_mem msC) mdC mt (x_mtn cx) (mt + 20 * Z.of_nat (length t)) 20 HARC Imt ltac:(lia)
        ltac:(rewrite RQ; unfold x_mtn, seg_spec.MVLAN_SIZE; lia)).
    - intros Hpos. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W (ms_mem msC) mdC mt (x_mtn cx) (mt + 20 * Z.of_nat (length t)) 20 HARC Imt
        ltac:(lia) ltac:(rewrite RQ; unfold x_mtn, seg_spec.MVLAN_SIZE; lia) Hpos).
    - split; [unfold FO_V; lia|]. split; [unfold FO_V; lia|]. split.
      { intros a' Ha'. unfold FO_V in Ha'. split.
        - apply (aview_some_of_apresent SEGS). exact (proj1 (HFpC a' ltac:(lia))).
        - rewrite HspT. change ESTACK with 4096. lia. }
      split; [unfold FO_V; lia|].
      split.
      { unfold amem_range, FO_V. pose proof N11 as (_ & HN11).
        destruct HN11 as [Hl | [Hh _]]; [left; unfold kLowShadowBeg in Hl; rewrite C5; lia | right; rewrite C4; lia]. }
      split; [unfold FO_V; exact (s23l_v_addr _ _ HF8 ZSC)|].
      intros _. unfold FO_V. apply (s23l_hull_v _ (x_fr cx) 20 N8 ltac:(lia) ltac:(lia)).
      intros j Hj. apply (aview_some_of_apresent SEGS). exact (proj1 (HFSpC j ltac:(lia))). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H10b & HCPY & HKC & HPRS & HSAME).
  clear HS.
  (* back at 0x85b68 *)
  assert (KC2 : forall a', 0 <= a' < 2 ^ 64 -> ~ (mt + 20 * Z.of_nat (length t) <= a' < mt + 20 * Z.of_nat (length t) + 20) ->
    ~ (x_s1 cx - 4096 <= a' < x_s1 cx) -> rdW W mem2 a' = rdW W (ms_mem msC) a').
  { intros a' Ha' H1 H2. apply HKC; [exact Ha' | exact H1 | change ESTACK with 4096; lia]. }
  assert (Q9 : getr regs2 9 = w64 (x_s1 cx)).
  { rewrite (s23m_pres' _ _ 9%bv 9 HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
    rewrite (RR 9%bv ltac:(s23m_in)). exact G9. }
  assert (H104' : rdword (rdW W mem2) (x_s1 cx + 104) = Some a).
  { apply (s23_kept_word (rdW W mem0)); [|exact H104]. intros x Hx.
    rewrite KC2 by (clear - Hx N1 N2 Mt4 Mtc N13 C1; lia). apply KC0; [lia | unfold s23_scr; lia]. }
  assert (H176' : rdword (rdW W mem2) (x_s1 cx + 176) = Some SHADOW_OFF).
  { apply (s23_kept_word (rdW W mem0)); [|exact H176]. intros x Hx.
    rewrite KC2 by (clear - Hx N1 N2 Mt4 Mtc N13 C1; lia). apply KC0; [lia | unfold s23_scr; lia]. }
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTKP2 & _).
  pose proof (s23m_seedP W regs2 mem2 (x_s1 cx) a Q9 ltac:(lia) ltac:(lia) Ra0 H104' H176'
    ltac:(intros o Ho; apply (apresent_writable SEGS); apply HSTKP2; rewrite HSTK; lia)) as HSP.
  assert (HEIP : img_env VAL A_LIM (s23_E regs2 [a; SHADOW_OFF])) by apply s23_E_img.
  assert (UP9 : bv_unsigned (ew (s23_E regs2 [a; SHADOW_OFF]) 9) = x_s1 cx)
    by (rewrite (s23_E_reg _ _ 9 9%bv eq_refl), Q9; apply unsigned_lit_small; lia).
  assert (EP32 : ew (s23_E regs2 [a; SHADOW_OFF]) 32 = Z_to_bv 64 a)
    by (exact (s23_E_val regs2 [a; SHADOW_OFF] 0 ltac:(unfold A_TEXT; lia))).
  assert (EP33 : ew (s23_E regs2 [a; SHADOW_OFF]) 33 = Z_to_bv 64 SHADOW_OFF)
    by (exact (s23_E_val regs2 [a; SHADOW_OFF] 1 ltac:(unfold A_TEXT; lia))).
  assert (EP18 : ew (s23_E regs2 [a; SHADOW_OFF]) 18 = w64 (Z.of_nat (length t) + 1)).
  { rewrite (s23_E_reg _ _ 18 18%bv eq_refl).
    rewrite (s23m_pres' _ _ 18%bv 18 HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)). exact T18. }
  remember (s23_E regs2 [a; SHADOW_OFF]) as EP eqn:HEP.
  (* 0x85b68 .. 0x85b78: a5 := the shadow base, 104(s1) := a + 1, 120(s1) := mn + 1 *)
  paj_run_to_sh RUNTOP HSP HJ2 0xe48.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
    eapply awr_ok_cons_stack_off with (n := 9%nat) (d := x_s1 cx - x_sp0 cx);
      [reflexivity | rewrite UP9; lia | cbn [YP09.r_wlo]; rewrite HSTK; lia | cbn [YP09.r_whi]; lia |].
    eapply awr_ok_cons_stack_off with (n := 9%nat) (d := x_s1 cx - x_sp0 cx);
      [reflexivity | rewrite UP9; lia | cbn [YP09.r_wlo]; rewrite HSTK; lia | cbn [YP09.r_whi]; lia |].
    apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  rename HF into HFP, HFr into HFrP, HG into HGP.
  s23_mdv. rename ms into msP, mdv into mdP.
  assert (KP : forall a', 0 <= a' < 2 ^ 64 -> ~ (x_s1 cx + 104 <= a' < x_s1 cx + 112) ->
    ~ (x_s1 cx + 120 <= a' < x_s1 cx + 128) -> rdW W (ms_mem msP) a' = rdW W mem2 a').
  { intros a' Ha' N1' N2'.
    apply (kept_of_frame EP _ (w_H W) mem2 (ms_mem msP)
      (fun x => (x_s1 cx + 104 <= x < x_s1 cx + 112) \/ (x_s1 cx + 120 <= x < x_s1 cx + 128)) HFrP);
      [| exact Ha' | intros [Hq' | Hq']; contradiction].
    intros b wlo whi x Hin Hx.
    lazymatch type of Hin with In _ (windows ?rs) => let w := eval vm_compute in (windows rs) in
      change (In (b, wlo, whi) w) in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [Hq' | Hin]; [injection Hq' as <- <- <-; cbn [base_val] in Hx; rewrite ?UP9 in Hx;
      cbv beta; lia |]).
    destruct Hin. }
  lazymatch type of HSP with st_ok_pi _ _ _ ?ssx _ =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
    let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
    pose proof (PaLibG.st_ok_pi_region_nth EP ssx (restrict (w_H W) msP) 0%nat r0 HSP ltac:(vm_compute; reflexivity)) as RP0;
    pose proof (PaLibG.st_ok_pi_region_nth EP ssx (restrict (w_H W) msP) 1%nat r1 HSP ltac:(vm_compute; reflexivity)) as RP1
  end.
  destruct RP0 as (_ & _ & _ & CP0). destruct RP1 as (_ & _ & _ & CP1).
  cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in CP0, CP1. rewrite UP9 in CP0, CP1.
  assert (UP32 : U EP (SOff 32 0) = a) by (apply U_atom; [exact EP32 | lia]).
  assert (HP104 : rdword (rdW W (ms_mem msP)) (x_s1 cx + 104) = Some (a + 1)).
  { apply (s23m_rd_chunk8 EP (w_H W) (ms_mem msP) (x_s1 cx) 104 _ (SAluw ALU_ADD (SOff 32 0) (SLit 1)) _ _ CP0);
      [s23m_in | reflexivity | | lia].
    apply s23_denot_of_U; [apply s23m_U_addw1; [exact UP32 | lia] | lia]. }
  assert (HP120 : rdword (rdW W (ms_mem msP)) (x_s1 cx + 120) = Some (Z.of_nat (length t) + 1)).
  { apply (s23m_rd_chunk8 EP (w_H W) (ms_mem msP) (x_s1 cx) 120 _ (SOff 18 0) _ _ CP1);
      [s23m_in | reflexivity | | lia].
    apply s23_denot_of_U; [apply U_atom; [exact EP18 | lia] | lia]. }
  (* every byte outside s23_D0 is the K85ac4 state's *)
  assert (KFIN : forall a', 0 <= a' < 2 ^ 64 -> ~ s23_D0 cx mt (length t) a' -> rdW W (ms_mem msP) a' = rdW W mem0 a').
  { intros a' Ha' HD0. unfold s23_D0 in HD0.
    rewrite KP by (first [exact Ha' | intros Hq'; apply HD0; tauto]).
    rewrite KC2 by (first [exact Ha' | intros Hq'; apply HD0; tauto
                          | intros Hq'; apply HD0; left; unfold s23_scr; change ESTACK with 4096; lia]).
    apply KC0; [exact Ha' | intros Hq'; apply HD0; left; exact Hq']. }
  (* mt[mn] holds v's 20 bytes: (par, vid) as an entry of the model's table *)
  assert (HKK : forall k0, 0 <= k0 < 20 ->
    rdW W (ms_mem msP) (mt + 20 * Z.of_nat (length t) + k0) = rdW W mem0 (x_fr cx + FO_V + k0)).
  { intros k0 Hk0. rewrite KP by (clear - Hk0 N1 Mt4 Mtc N13 C1 Hc; lia). rewrite (HCPY k0 Hk0).
    apply KC0; [unfold FO_V; lia | unfold s23_scr, FO_V; change ESTACK with 4096; lia]. }
  assert (Hnn : forall i0, 0 <= i0 < Z.of_nat 20 -> rdW W (ms_mem msP) (mt + 20 * Z.of_nat (length t) + i0) <> None).
  { intros i0 Hi0. change (Z.of_nat 20) with 20 in Hi0.
    rewrite KP by (clear - Hi0 N1 Mt4 Mtc N13 C1 Hc; lia). rewrite (HCPY i0 Hi0).
    apply (aview_some_of_apresent SEGS). exact (proj1 (HFpC (x_fr cx + FO_V + i0) ltac:(unfold FO_V; lia))). }
  destruct (s23_bytes_of_rd SEGS (w_H W) (ms_mem msP) (mt + 20 * Z.of_nat (length t)) 20 Hnn) as (f & Hfl & Hfb).
  assert (Hstrz : sa_strz (rdW W (ms_mem msP)) (mt + 20 * Z.of_nat (length t)) par).
  { split; [|exact (proj2 Hv)].
    apply (s23m_zs_xfer (rdW W mem0) _ (x_fr cx + FO_V) _ _ 20 HKK); [rewrite length_app; cbn [length]; lia | exact (proj1 Hv)]. }
  assert (Hval : sa_val (rdW W (ms_mem msP)) (mt + 20 * Z.of_nat (length t) + 16) 4 vid).
  { apply (s23m_val_xfer (rdW W mem0) _ (x_fr cx + FO_VID) _ 4 vid 4); [|lia | exact Hvid].
    intros k0 Hk0. replace (mt + 20 * Z.of_nat (length t) + 16 + k0) with (mt + 20 * Z.of_nat (length t) + (16 + k0)) by lia.
    replace (x_fr cx + FO_VID + k0) with (x_fr cx + FO_V + (16 + k0)) by (unfold FO_V, FO_VID; lia).
    apply HKK. lia. }
  pose proof (s23_mvlan_of (rdW W (ms_mem msP)) (mt + 20 * Z.of_nat (length t)) par vid f Hstrz Hpl Hval
    ltac:(lia) Hfl Hfb) as Henc.
  pose proof Htabs as (_ & _ & _ & _ & Hmtab0 & _).
  assert (Hmtab' : sa_mtab (rdW W (ms_mem msP)) mt (t ++ [(par, vid)])).
  { apply (s23_mtab_snoc (rdW W mem0) (rdW W (ms_mem msP)) mt t (par, vid) f Hmtab0); [|exact Hfl | exact Hfb | exact Henc].
    intros i0 Hi0. apply KFIN; [lia|]. unfold s23_D0, s23_scr. change ESTACK with 4096.
    intros [Hq1|[Hq1|[Hq1|Hq1]]]; clear - Hi0 Hq1 N1 N3 N13 Mtc Mt4 C1 Hc; lia. }
  (* the join 0x85b7c *)
  pmkst HSP.
  change (SRr SEGS W (cfg_at SEGS (BASE + 0xe48) (ms_regs msP) (ms_mem msP) mdP) (lt_post B MT cx)).
  apply (HPJ cx ly S W regs0 mem0 md0 k acc c m tab mt par vid (ms_regs msP) (ms_mem msP) mdP CTX);
    rewrite ?HD; cbn [fst snd].
  + split; [exact HJ2|]. split; [|exact KFIN].
    intros r Hr. unfold S23_RLKJ in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [ lazymatch goal with
        | |- getr _ 15%bv = getr _ 15%bv =>
          rewrite R15; s23_vreg HSP (15%bv : bv 5); apply U_atom; [exact EP33 | unfold SHADOW_OFF; lia]
        | |- getr _ ?r = getr _ ?r =>
          transitivity (getr regs2 r); [s23_kreg_goal HSP HEP|];
          let z := eval vm_compute in (bv_unsigned r) in
          rewrite (s23m_pres' _ _ r z HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity));
          apply RR; s23m_in
        end |]).
    destruct Hr.
  + lia.
  + exact HP104.
  + rewrite length_app, Nat2Z.inj_add. cbn [length]. exact HP120.
  + exact Hmtab'.
  + rewrite length_app, Nat2Z.inj_add. cbn [length]. lia.
Qed.

(* ---- the scan: every turn j, by the step from j + 1 down from 40 (the table has at most cap < 40 entries) ---- *)
Lemma s23_loop_all : S15_X38 B MT i ->
  (forall j, S15_X38 B MT i -> S15_LOOP B MT i (Datatypes.S j) -> S15_LOOP B MT i j) ->
  forall j, S15_LOOP B MT i j.
Proof.
intros HX STEP.
assert (HV : forall j, (40 <= j)%nat -> S15_LOOP B MT i j).
{ intros j Hj. unfold S15_LOOP.
  intros cx ly S W regs0 mem0 md0 k acc c m tab mt par vid regs mem md CTX _ Hjt. exfalso.
  destruct CTX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htabs & _).
  destruct Htabs as (H1 & _ & _ & _ & _ & H6). lia. }
assert (HD : forall d j, (j + d = 40)%nat -> S15_LOOP B MT i j).
{ induction d as [|d IH]; intros j Hjd; [apply HV; lia|].
  apply STEP; [exact HX|]. apply IH. lia. }
intros j. destruct (Nat.le_gt_cases 40 j) as [Hj|Hj]; [apply HV; exact Hj|]. apply (HD (40 - j)%nat). lia.
Qed.
End i.

(* ---- the segment lemma, from the pieces: the join (S15_PJ), the copy or the full table (S15_X40), the scan's
   step (S15_LOOP), the scan's end (s23_x38) and the turn's head (s23_top) ---- *)
Lemma s23_compose :
  (forall i, LTA_K858f4 B MT (Datatypes.S i) -> LTA_K85bd0 B MT -> S15_PJ B MT i) ->
  (forall i, LTA_K85bd0 B MT -> S15_PJ B MT i -> S15_X40 B MT i) ->
  (forall i j, S15_X38 B MT i -> S15_LOOP B MT i (Datatypes.S j) -> S15_LOOP B MT i j) ->
  lt_seg_S15_stmt B MT.
Proof.
intros PPJ PX40 PSTEP. unfold lt_seg_S15_stmt. intros i HK8 HKB.
pose proof (PPJ i HK8 HKB) as HPJ.
pose proof (PX40 i HKB HPJ) as HX40.
pose proof (s23_x38 i HPJ HX40) as HX38.
apply (s23_top i); [|exact HX40].
exact (s23_loop_all i HX38 (PSTEP i) 0%nat).
Qed.

Theorem lt_seg_S15 : lt_seg_S15_stmt B MT.
Proof. exact (s23_compose s23j_pj s23m_x40 s23l_step). Qed.
End d.
Print Assumptions lt_seg_S15.
