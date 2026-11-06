(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec StoreOk HeapIface L5Defs L5Core PmLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_PmModel () := "C47Corelib7Classes?RelationClasses;reflexivityc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM5p_stkC13~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM6p_moreC13~~~I47Corelib4Init5Logic2eq00c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM6p_doneC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM7p_depthC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM;stack_shapeC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM4p_tbC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM4p_tgC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM5tb_okC13~~~I47Corelib4Init5Logic3and00C47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z7add_0_rC47Corelib4Init5Logic8eq_ind_rc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM3invC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM5inv_dC13~~~i89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM3pst00C13~~~I47Corelib7Numbers7BinNums1Z00i89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM6pstate00C13~~~K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01C47Corelib7Classes?RelationClasses=iff_ReflexiveC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op203c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM6tb_lawC13~~~K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib6ZArith:ZArith_dec;Z_le_gt_decC56Stdlib6ZArith6BinInt1Z2gtI47Corelib4Init6Specif7sumbool00C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr05K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C47Corelib4Init5Logic9False_indK46Stdlib9micromega7EnvRing5PExpr04C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z9pow_add_rC47Corelib4Init5Logic6eq_indK47Corelib4Init5Logic2ex01C56Stdlib6ZArith6BinInt1Z6divideC56Stdlib6ZArith6BinInt1Z:mod_divideC56Stdlib5omega8PreOmega1Z:divide_altI47Corelib4Init5Logic2ex00c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM8pow2_posC13~~~C56Stdlib6ZArith6BinInt1Z<divide_transK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega3Op206K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic5False00".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PM.

(* [comment removed for export] *)
Definition zeros_at (M : word -> option byte) (a n : Z) : Prop :=
  forall i, 0 <= i < n -> M (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0).

Section Model.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable A : pm_addrs.
Variable acc : (word -> option byte) -> Z -> Z -> Prop.
Variable ann : (word -> option byte) -> Z -> Z -> Z -> Prop.

(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive vstr : Type := VShort (n : Z) | VLong (cnt n p : Z).
Definition vs_size (s : vstr) : Z := match s with VShort n => n | VLong _ n _ => n end.
Definition vs_cap (s : vstr) : Z := match s with VShort _ => 22 | VLong c _ _ => c - 1 end.
Definition vs_data (o : Z) (s : vstr) : Z := match s with VShort _ => o + 1 | VLong _ _ p => p end.
Definition vs_own (s : vstr) : list (Z * Z) := match s with VShort _ => [] | VLong c _ p => [(p, c)] end.

Definition vstr_at (M : word -> option byte) (o : Z) (s : vstr) : Prop :=
  L5.defined M o 24 /\ acc M o 24 /\
  match s with
  | VShort n => 0 <= n <= 22 /\ L5.u8_at segs M o (2 * n)
  | VLong c n p => L5.u64_at segs M o (c + 1) /\ L5.u64_at segs M (o + 8) n /\ L5.u64_at segs M (o + 16) p
                   /\ 0 <= n < c /\ 26 <= c <= 2 ^ 27 /\ c mod 2 = 0 /\ L5.defined M p c /\ acc M p c
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record pstate : Type := PS { ps_mode : Z; ps_len : Z; ps_type : Z; ps_idx : Z }.
Definition ps_root : pstate := PS 0 0 0 0.
Definition MAX_ITEMS : Z := 2 ^ 24.
Definition MAX_DEPTH : Z := 1024.

Definition mode_counted (m : Z) : Prop := m = 2 \/ m = 4 \/ m = 5 \/ m = 6 \/ m = 7 \/ m = 8.
Definition mode_indef (m : Z) : Prop := m = 3 \/ m = 9 \/ m = 10.
Definition mode_bottom (m : Z) : Prop := m = 0 \/ m = 1.
(* [comment removed for export] *)
Definition mode_flag (m : Z) : Z := if (Z.eqb m 0 || Z.eqb m 6 || Z.eqb m 8 || Z.eqb m 10)%bool then 1 else 0.

Definition pstate_ok (s : pstate) : Prop :=
  0 <= ps_type s < 256 /\
  (   (mode_counted (ps_mode s) /\ 0 <= ps_idx s <= ps_len s /\ ps_len s <= MAX_ITEMS)
   \/ (mode_indef (ps_mode s) /\ ps_len s = 0 /\ 0 <= ps_idx s <= MAX_ITEMS)
   \/ (mode_bottom (ps_mode s) /\ ps_len s = 0 /\ ps_idx s = 0)).

Definition pstate_at (M : word -> option byte) (a : Z) (s : pstate) : Prop :=
  L5.u32_at segs M a (ps_mode s) /\ L5.u64_at segs M (a + 8) (ps_len s) /\ L5.u8_at segs M (a + 16) (ps_type s) /\ L5.u64_at segs M (a + 24) (ps_idx s).

(* [comment removed for export] *)
Definition vec_at (M : word -> option byte) (v b k : Z) (stk : list pstate) : Prop :=
  L5.u64_at segs M v b /\ L5.u64_at segs M (v + 8) (b + 32 * Z.of_nat (length stk)) /\ L5.u64_at segs M (v + 16) (b + 32 * 2 ^ k)
  /\ 0 <= k <= 11 /\ Z.of_nat (length stk) <= 2 ^ k /\ b mod 16 = 0
  /\ L5.defined M b (32 * 2 ^ k) /\ acc M b (32 * Z.of_nat (length stk)) /\ ann M b (32 * Z.of_nat (length stk)) (32 * 2 ^ k)
  /\ (forall i, (i < length stk)%nat -> pstate_at M (b + 32 * Z.of_nat i) (nth i stk ps_root)).
Definition vec_own (b k : Z) : list (Z * Z) := [(b, 32 * 2 ^ k)].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CHUNK : Z := 16384.
Record srcst : Type := SRC { sr_qc : Z; sr_de : Z; sr_rem : Z }.
Definition src_fields_at (M : word -> option byte) (os isp sbp : Z) (s : srcst) : Prop :=
  L5.u64_at segs M (os + 240) isp /\ L5.u64_at segs M (os + 248) sbp /\ L5.defined M (os + 256) 8
  /\ L5.u64_at segs M (os + 264) (sr_qc s) /\ L5.u64_at segs M (os + 272) CHUNK
  /\ L5.u64_at segs M (os + 280) (sr_de s) /\ L5.u64_at segs M (os + 288) (sr_rem s)
  /\ sr_qc s <= sr_de s /\ 0 <= sr_rem s /\ sr_de s + sr_rem s <= sr_qc s + CHUNK
  /\ sr_qc s mod 16 = 0 /\ L5.defined M (sr_qc s) CHUNK /\ acc M (sr_qc s) CHUNK /\ acc M (os + 240) 56.
Definition src_own (s : srcst) : list (Z * Z) := [(sr_qc s, CHUNK)].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition iosb_at (M : word -> option byte) (o vp rdb st : Z) : Prop :=
  L5.u64_at segs M o vp /\ L5.u32_at segs M (o + 32) st /\ L5.u32_at segs M (o + 36) 0 /\ L5.u64_at segs M (o + 40) rdb
  /\ L5.u64_at segs M (o + 48) (pa_classic_imp A) /\ zeros_at M (o + 56) 80 /\ L5.defined M o 152 /\ acc M o 152
  /\ (st = 0 \/ st = 2).

(* [comment removed for export] *)
Record strm : Type := STRM { sm_g : Z; sm_eg : Z; sm_st : Z }.
Definition iss_at (M : word -> option byte) (ois : Z) (str : vstr) (s : strm) : Prop :=
  L5.u64_at segs M ois (pa_vp_iss A) /\ L5.defined M ois 120 /\ acc M ois 120
  /\ L5.u64_at segs M (ois + 16) (pa_vp_strbuf A)
  /\ L5.u64_at segs M (ois + 24) (pa_classic_imp A)
  /\ L5.u64_at segs M (ois + 32) (vs_data (ois + 80) str) /\ L5.u64_at segs M (ois + 40) (sm_g s) /\ L5.u64_at segs M (ois + 48) (sm_eg s)
  /\ L5.u64_at segs M (ois + 64) 0
  /\ vstr_at M (ois + 80) str
  /\ L5.u64_at segs M (ois + 104) (sm_eg s) /\ L5.u32_at segs M (ois + 112) 8
  /\ iosb_at M (ois + 120) (pa_vp_iss_ios A) (ois + 16) (sm_st s)
  /\ sm_eg s = vs_data (ois + 80) str + vs_size str /\ vs_data (ois + 80) str <= sm_g s <= sm_eg s.

(* [comment removed for export] *)
Definition nullis_at (M : word -> option byte) (o : Z) : Prop :=
  L5.u64_at segs M o (pa_vp_nullis A) /\ L5.defined M o 80 /\ acc M o 80
  /\ L5.u64_at segs M (o + 16) (pa_vp_nullbuf A) /\ L5.u64_at segs M (o + 24) (pa_classic_imp A)
  /\ iosb_at M (o + 80) (pa_vp_nullis_ios A) (o + 16) 0.

(* [comment removed for export] *)
Definition unread (src : srcst) (sm : strm) : Z := sr_rem src + (sm_eg sm - sm_g sm).

(* [comment removed for export] *)
(* [comment removed for export] *)
Record pst : Type := PST {
  p_more : Z; p_done : Z; p_depth : Z;
  p_src : srcst;
  p_tb : vstr;             (* [comment removed for export] *)
  p_tg : Z;                (* [comment removed for export] *)
  p_b : Z; p_k : Z; p_stk : list pstate   (* [comment removed for export] *)
}.

Definition parser_at (M : word -> option byte) (op ois : Z) (s : pst) : Prop :=
  L5.u64_at segs M op (pa_vp_parser A) /\ L5.defined M op 384 /\ acc M op 24
  /\ L5.u8_at segs M (op + 8) (p_more s) /\ L5.u8_at segs M (op + 9) (p_done s) /\ L5.u32_at segs M (op + 12) (p_depth s)
  /\ L5.u8_at segs M (op + 16) 0 /\ L5.u32_at segs M (op + 20) 0
  /\ nullis_at M (op + 32)
  /\ src_fields_at M (op + 24) ois (ois + 16) (p_src s)
  /\ L5.u32_at segs M (op + 320) MAX_DEPTH /\ L5.u64_at segs M (op + 328) MAX_ITEMS /\ acc M (op + 320) 64
  /\ vstr_at M (op + 336) (p_tb s)
  /\ vec_at M (op + 360) (p_b s) (p_k s) (p_stk s)
  /\ (p_more s = 0 \/ p_more s = 1) /\ (p_done s = 0 \/ p_done s = 1) /\ 0 <= p_depth s <= MAX_DEPTH + 1.

(* [comment removed for export] *)
Definition parser_own (s : pst) : list (Z * Z) := src_own (p_src s) ++ vec_own (p_b s) (p_k s) ++ vs_own (p_tb s).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tb_law (c : Z) : Prop :=
  exists j, 0 <= j <= 13 /\ c < 2 ^ (15 + j) /\ (j = 0 \/ 2 ^ (14 + j) <= c) /\ c mod 2 ^ (3 + j) = 0.
Definition tb_ok (s : vstr) (tg : Z) : Prop :=
  0 <= tg <= 23 /\ 21 * 2 ^ tg <= vs_cap s /\
  match s with VShort _ => tg = 0 | VLong c _ _ => tb_law c /\ 1 <= tg end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition stack_shape (stk : list pstate) : Prop :=
  (1 <= length stk)%nat /\ Z.of_nat (length stk) <= MAX_DEPTH + 1
  /\ mode_bottom (ps_mode (nth 0 stk ps_root))
  /\ (forall i, (1 <= i < length stk)%nat -> ~ mode_bottom (ps_mode (nth i stk ps_root)))
  /\ (forall i, (i < length stk)%nat -> pstate_ok (nth i stk ps_root)).

Definition inv (s : pst) : Prop :=
  p_more s = 1 /\ p_done s = 0 /\ p_depth s = Z.of_nat (length (p_stk s)) - 1 /\ stack_shape (p_stk s) /\ tb_ok (p_tb s) (p_tg s).
(* [comment removed for export] *)
Definition inv_d (d : Z) (s : pst) : Prop :=
  p_more s = 1 /\ p_done s = 0 /\ p_depth s = Z.of_nat (length (p_stk s)) - 1 + d /\ stack_shape (p_stk s) /\ tb_ok (p_tb s) (p_tg s).
Lemma inv_d0 s : inv s <-> inv_d 0 s.
Proof.
ltac2:(KReplay.run1 (kr_t_PmModel ()) ["Model"] "h01sh11zp;1p;2p;3p;4p;6p-1g0000R0p4p710p9g000^j1:Tg001ij2=Tg002Ij13Tg002ij1>Tg003Gj27Tg003dj1;Tg0050j31Tg005Jj14Tg006Vj15Tg007cj16Tg0094j12Tg00:>j18Tg00;Hj29Tg00<Sj20Tg00<nR1j2<TP0j4DTg00=Gj2CTg00=dj1BTg00>Ej6ATg00>cj1?Tg00?lj2@Tg00A7R0g00BBR2g00B`R3f0R4#:R5'=#3g00Cn#>R6'7R7f1R8#;=126R9%48g00DSR:512R;%58R<%:8R=,=3#3/76512%6=%28%88'9'0R8'0'0'0A12<4/08,0;,09'<X12p-0P1g00E1%;4=126%44=12:%54=127%65%24%84'9'0'0'0'0CD1C7:%B7EA%?41@:4'<eX00P4O1W0o"). Qed.

(* [comment removed for export] *)
Definition ps_weight (s : pstate) : Z := ps_len s - ps_idx s.
Definition stk_weight (stk : list pstate) : Z := fold_right (fun s w => ps_weight s + w) 0 stk.
Definition top_flag (stk : list pstate) : Z := mode_flag (ps_mode (last stk ps_root)).
Definition mu (s : pst) (sm : strm) : Z :=
  (unread (p_src s) sm * 2 ^ 35 + stk_weight (p_stk s)) * 4096 + 2 * Z.of_nat (length (p_stk s)) + top_flag (p_stk s).
(* [comment removed for export] *)
Definition mu_src (src : srcst) (sm : strm) : Z := 2 * unread src sm + (if Z.eqb (sm_st sm) 0 then 1 else 0).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pot_stack (L : heap_layout) (k : Z) : credit :=
  (hl_k_per_malloc L * (11 - k), 32 * (2 ^ 12 - 2 ^ (k + 1)) + (11 - k) * hl_b_overhead L).
Definition pot_text (L : heap_layout) (s : vstr) (tg : Z) : credit :=
  (hl_k_per_malloc L * (23 - tg), (2 ^ 28 + 64 - 2 * vs_cap s - tg) + (23 - tg) * hl_b_overhead L).
Definition credit_add (c d : credit) : credit := (fst c + fst d, snd c + snd d).
Definition pot_parser (L : heap_layout) (s : pst) : credit := credit_add (pot_stack L (p_k s)) (pot_text L (p_tb s) (p_tg s)).
(* [comment removed for export] *)
Definition cost1 (L : heap_layout) (n : Z) : credit := (hl_k_per_malloc L, n + hl_b_overhead L).
(* [comment removed for export] *)
Definition pot_call (L : heap_layout) (n : Z) : credit :=
  credit_add (credit_add (cost1 L (n + 16)) (cost1 L (n + 32)))
    (credit_add (credit_add (cost1 L CHUNK) (cost1 L 32)) (credit_add (pot_stack L 0) (pot_text L (VShort 0) 0))).

End Model.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pow2_pos k : 0 <= k -> 0 < 2 ^ k.
Proof.
ltac2:(KReplay.run1 (kr_t_PmModel ()) [] "h07__arithh14__ffh28__varmaph35__with44__x1h51kh61Hp;2p;1p;4p;3p;8p;7g00Eaj23Tg00F=j1GTg002ij16Tg00Fbj14Tg00GBj1FTg00Gbj1:Tg00H@j17Tg00H^j15Tg00IIj22Tg00Ilj40Tg00JWj28Tg00K9j29Tg00KSj2ETg0050j3DTg00L?j3;Tg00L^j4<Tg00MPj2=Tg00Mlj2>Tg00NJj2?Tg00Nmj1@Tg00OOj8ATg00P3j4BTg00P[j7CTf1R0g00Q?R1g00Q^R2P2g00R>R3f0R4g00R^FCp=1g00BBR5g00DSR6/34R7g00CnR8#G#6R9P0g00S>R:#4R;%F:R:%:5%75R<%55R=P51256R>g00Sj1259C0'118=3R?P4f2R@g00TQRAg00U1RB'91E4@=DABdA;560C<RBb1b2b31=69P4b0P;P:1>50P<P=P1P2P2P3P5P>g00UQ1?58C0,1=R=%@2P=GAP?PBb1b2b3X451360\7^45P4P@P0O2b0CBW6X55P4O1W5o"). Qed.

(* [comment removed for export] *)
Lemma tb_law_request c need :
  tb_law c -> 26 <= c -> c - 1 < need -> need < 2 ^ 26 + 16384 -> need <= c - 1 + 16384 ->
  Z.max (2 * (c - 1)) need < 2 ^ 27.
Proof.
ltac2:(KReplay.run1 (kr_t_PmModel ()) [] "p'0h02Hah11Hh24__x1h32H0h42H1h52H2h62H3h71qh81rh97__arithh:4__ffh;8__varmaph<5__with=1zh>4__p1h?4__x2h@2H4hA7__sat16hB7__sat17hC7__sat18hD7__sat19hE7__sat20hF7__sat21hG4__p2hH4__p3hI7__sat13hJ7__sat14hK7__sat15hL4__x3hM4__x4hN4__x5hO4__x6hP2HdhQ4__x7hR1ahS1bhT1xi001xhU2H5hV6__sat1hW6__sat2hX7__sat22hY7__sat23hZ6__sat3h[6__sat4h\6__sat5h]6__sat6h^6__sat7h_6__sat8h`4Hm15ha6__sat0hb1chc1jhd4needhe2q0hf1si011shg3H10hh3H27hi2H6hj2H7hk2H8hl2H9hm2Hchn4Hc26ho5Hgrowhp3Hgthq2Hjhr4Hj12hs3Hleht3Hlohu3Hlthv4Hmodhw5Hneedhx2Hqhy5Hstephz7__sat24h{7__sat25h|7__sat26h}7__sat27h~7__sat28i027__sat29i037__sat30i047__sat31i057__sat32i067__sat33i077__sat34i086__sat9i092r0i0:3z27i0;1gi0<1lp%0p%1p&0p;1p;2p;3p;4p;5p;8p;6p;7g00V8k10^Tg00WDj1cTg00F=j1>Tg002ij1BTg00Eaj23Tg00=Gj21Tg00Wij26k10KTg00<SS00j2?Tg003Gj2=Tg00MPj28Tg00XFj2ETg00Xcj2gTg00Y@k209Tg00Ygj2STg00ZCR0k208Tg00Zcj2_Tg00[Tj25Tg00P3j2<Tg00\4j3;Tg00\Xj2NTg00]9j1GTg00]Rj2:Tg00]oj2RTg00^Vj2OTg00_=j2WTg00_cj2ZTg00Fbk10XTg00GBk10WTg00Gbk10VTg00H@k10UTg00H^k10TTg00IIk20<Tg00JWk20STg00K9k20;Tg00KSk20RTg0050j3iTg00L?k30PTg00L^k40OTg00NJk20:Tg00Nmk10NTg00`Ik50MTg00a0k100Tg00aNj2~Tg00aoj1DTg00bNj3sTg00c7j3lTg00cZk107Tg00d8k306Tg00d[k205Tg00e:j3{Tg00e]k80ITg00f:k50HTg00f]k60GTg00g9k40FTg00gSj2kTg00h3k30ETg00hWj3xTg00i<S01j2yTg00iVk10DTg00jdk50CTg00kJj2zTg00l3k204Tg00l\k20BTg00mHk20LTg00mjk201Tg00nDk70@Tg00Ilj4`Tg00P[j7dTg00Mlk20?Tg00nhk30QTg00OOj8bTg00oKj3wTg0104k20>Tg010`k30=Tg011@k40]Tg011^k60\Tg012Bk70[Tg012fk60ZTg013Jk30YTg00DSR1f1R2'3f0R3'?p=vf2R41123'6p=4g00BBR5?i31p=21323-014p=]1523=i51p=F1842/?3p=j%>3#>p>03%>3#>#>#>p=u1313p=01813p=91623,31p=K1623,81p=Lf3R61E42/135i5p=C13141823'?p=U1831p=X18421331'?p=VAi523p=720<53p=MP4g00Q?R7g00Q^R8P8g00R>R9P5P2g00SjR:P3C`g00R^R;Fdp=a20?53p=hP5P2g0143P3C`p>02B0Q523p=TP4P7P8P8P9P5P2g00UQR<P3C`P;Fdp=If4R=P7P8P8P9P6P7P8P8P9P4P;FdP2P3Gbp=Y20453p=JAw523p=fAw523g014Z+0>p=\g00S>R>B0=>2380=4p=^P5P4P2P3H0]p=@20:53p=[P4P7P8P8P9P5P2g015FR?P3C`P;Fdp=AP5P2P?P3C`p=}P=P7P8P8P9P6P4P2P7P8P8P9P3P;FdGbp=rP6P7P8P8P9P4P2P3Gbp=mP2P7P8P8P9P3J0\p=nP4P7P8P8P9P2P3K0[p=PP2P7P8P8P9P3J0Zp=qf6R?P7P8P8P9f5R@P=P6P7P8P8P9P4P2P3GbGbp=QP5P2P:P3C`p=pP?P7P8P8P9P@P7P8P8P9P=P6P4GbP2P3Gbp=H1823,?4p=|11239i54p>0JP5P2P<P3C`p=oB0Y523p=eAw5239w54p=tP2P7P8P8P9P3P;Fdp>0A&0^2Q01P5g00CnR;#cR<#>S02#cR:#BRA,33,v3RB%>;S03#BRC%c<RD#cS04#BRE;43RF%23S05%>D#BRG=4C3RH;]6%B<RI/13S06,6CRJ,F6'?5j6'?Xc5%>:S07#BRK/36%B;RL,==/8616CKRMQ03#>S08#>S09#>$03#u#uS0:#BRN'1RO,8=1=?L/1N,3@f7RP/=L,ECS0;/g?%c:#B,6CR:'8[[[[P3Q05?]H@1F@J'?9j@F,?BQ00%02S0<132A'?11E2S0=,6C%22A4CG2;]?11I2S0>,6C,F?'?5j?13KPf8RB/=L/8P18BOf9RFf:RJ/=LS0?/1N'3f;RH/=L,EC/gJ/8:[[[[P3%06S0@136A'?A4CE=%2=S0AA4CG=;]FA4CI=,FF'?5jFQ00A4CE@,8J%2@S0BA4CG@;]J11I@S0C,6C,FJ'?13KHS0Df<RQ/=L/8H18QOf=S0Ef>S0F/=L/1N'3f?S0G/=L,ECQ0F'g/8:[[[[P3A4CEP,8Q%2BS0HA4CGBQ0E3]Q0EA4CIB'F'?Q00%2FA4CGFQ0F3]Q0FA4CIF'FQ0G,3Kf@S0I/=LQ0G'8Q0I/8OfAS0JfBS0K/=L/1N'3fCS0L/=LRR,ECQ0K'g/8:[[[[P3%2HS0MA4CGHQ0I3]Q0JA4CIQ'FQ0K,3KQ0K,8RQ0L/8OfDROfERR/=L/1N'3fFR:009M13:MS0N1S:M+08P0fGRS/3M1SSMfHS0O/3MRTP3P3XsTP3O1Q0O/SMfIRT/3MQ02#>#BRU009O13UOS0P1SUO+08P013UR1SUR13U:R0P3P3X10P3O11SU:13USPC11ESS0QPKfLR0A4CISS0R'_S0S%00Q0O,1IS0T,6CS0U#0S0VfNRV11ITS0W,6CS0X'5#0[[S0Y1<CKS0Z%9CRW%0K%9M[[S0[%0CRXg015mRYA;CK2UW0S0\%0M\Y^0XS0]fJS0^,1IS0_,<CS0`fKS0a,1IRZ#011I0S0b,6CS0c#9S0d[\WS0efMR[,1IR\=;C2VYX0XS0f16C\R]#0\Y^0XS0g11E0R^,<CS0h11E[R_#011EVS0i,6CR`#9[\WS0jfORa,1ES0k=;C2VYX0XS0lQ0k,KC\Y^0XS0m11GVS0n,<CS0o11GaRb#0fPS0p,1GS0q,LC[\WS0rfQRc,1GS0s=;C2VYX0XS0tQ0s,6CS0u#0\Y^0XS0vfURdQ0p,1IS0w,6CRe'NS0x%2e#GfVRf11IcS0y,6CRg1:fg15fgS0zCC[S0{1RfgS0|%9gfWRhfRRi94CIRj'5Rk?Ukj[S0}1OhjS0~%XjfSRl,1IS10,6CRmfXRn/5mRo;Vo[S111WnmS12%2mfYRpfTRq94CIRr':#2[S131ZprS14%2rRsfZRtA4CIdS15'5/7t[S16Q15,:tRuP5f[RvA4CIfS17'5RwP5&0X>Rx&0W>R>&0V5Ry&0U5Rz&0T5R{20<51R|%MCS183aS1920S{9S1:P3P4g00TQR}g00U1R~+0;20R34=i}~dB0P512H0OS1;b:b;b<PWP3b9b8b7b@b6b5b4b3babVbWbZb[b\b]b^b_Q0SQ0YQ0ZQ0[Q0\Q0]Q0`Q0eQ0fQ0gQ0hQ0jQ0lQ0mQ0oQ0rQ0tQ0vQ0xQ0{Q0|Q0}Q0~Q11Q12Q13Q14Q16PuP5PwP5PxP>%h2S16PzP{P{%MUS1420:5;R1+02&0N8R~%MER}/T1%MKS135I{DYQ1:Q1;b:b;b<X251SU3Q0=/3K[^25P3PnQ0JO2b9b8b7b@b6b5b4b3babVbWbZb[b\b]b^b_I0MQ0Q,6C/3MQ0U,_[S0=%0[Q0X#0Q0_,6CS0_,5a#0[[S12Q0ZQ0[Q0\Q0]Q0a,1ES11,<C%0^16C_S0~#9[\WQ0i=;C2VYX0X%0`\Y^0X1<C\11IVS0}#011IaS0|,6CR`#9S0{[\WQ0w=;C2VYX0X%0e\Y^0X1<CbQ0q#0Q0u#9[\W11GiS0u=;C2VYX0XQ0u,6CS0x#0\Y^0X1Nfg%2gS0v#GPhPj1:hjS0tPkCC[1Rhj%9jS0rAUoom[1Onm%Xm15prRk=Vrk[1Wpr%2u\sQ15,ZtQ15#217wv[Q17,:vP5f\RwA4CIhS0o'5P5p-0Rs&00;,~5S0mg016IS0l#DS0j#DR;#D#DRu#DS0h#DS0g#DS0f#DS0e#D#DS0`#J5s5%JuS1<%J;S1='f'\R;Q0h#JS0hQ1<Q0j#JS0j'f'\Ru?^ux7^;P>%h?S1>?@?y?@4y%h=S1?%h@S1@7@67@2PzP{P{%[DRD=A{|S1AP~P{Q03#cS1B#[S1CQ03#[R;'}DrS1DP~P{P{Q1AP~Q09#[S09=A{|S1ECmP~P{P{Aa{|DS1FP~1n{BQ1C=a{DS1G5P{P~P{P{Q1A,q{S1HP~Q099l5DQ1C'T9A{;P~P{P{Q19P~P{%MIS1I/T1S1J9I{|P~Q1FFQS1KP~P{%[<R<Q18Q07$076065Ru5I{P~P{P{202;uP~P{Q13=I{;S07P~P{Q1C=A{|S1LP~P{P{1p;<P~P{AI{|1S1M1n{FS1N5P{P~1n{JS1OCmDYFQDYFQFHFHFQQ1:Q1;b:b;b<X25X?5XL5XM5XN5XO5X>sXGsWHQ0A17=4[Q0B%2PRu[%9?S1PA|F?P[g016hS1Q\uS1RP@PBPFPPCC[Q0C#0%9J[\WS0C13PM1SPM13KBQ0M18JHQ0J,vJQ0L[[[[[[[[[[[^25^?5^L5^M5^N5^O5^>s^Gs^HsP3Q1Q13pAQ0<P4A4CIpRMP2A4CEpf^RuPpP6P=P?PPPHQ0JPRQ0aP0PcPdODb9b8b7bUb@b6b5b4bVbWbZb[b\b]b^b_c08b3+05W1P3O1n200110100021010<1110;bfQ0PP511I:S0P,6CS0M16CERp,E3S1S'7X=51=RUS1T,6CS1UP5Q1T/1ES1V,6CQ0M/73X=5P5P5&0KCS1WQ1W11IRS1XQ1VP5\5Q1W+0;Q0^Q1X,6CS1W'_S1VQ0^#0Q0M#0Q0R,50#0[[S1YQ0ZQ0[Q0\Q0]Q0T,<CS1ZQ0W#0Q0_#9[\WS0WA;CZ2VYX0XS1[16CZS1\#0\Y^0XS1]Q0^,1ES1^,<CS1_Q11#01LC^[\WS11A;C_2VYX0XS1`Q0~#0\Y^0XS0~11G0S1a,<CS1b11G[#0Q0n,LC[\WS0nA;Cb2VYX0XS1c1KCb\Y^0XS1dQ0},6CRb,NlS1e%2bS1f#GPqP`1:q`S1g15q`S1hCC[S1i1Rq`S1jQ0{15deS1kQ1k;Ue[S0{1OdeS1l%XeQ0zQ0z5Vg[S1m1WfgS1nQ0vQ0t#2[S0v1ZhjR_%2j17on[Ro1:nmR^P5PkP5PxP>Q16PzQ1JQ149{51RZ/T}5A{Q1:Q1;b:b;b<X25Q061=3U<0JE^25P3PfO1b9b8b7b6b5b4b3b1bIbJbKbAbBbCbDbEbFL0IQ1U/EpPCQ1TPEQ1VQ1YQ0ZQ0[Q0\Q0]Q1ZQ0WQ1[Q1]Q1_Q11Q1`Q0~Q1bQ0nQ1cQ1dQ1eQ1iQ1jQ0{Q1lQ1mQ1nQ0vP_PoP^P5PkP5PxP>Q16PzP{Q14=I{1S16P~P{1o|ZDrQ1:Q1;b:b;b<X2513U31=2U#0[^25P3PfQ0JO2b9b8b7b6b5b4b3b1bIbJbKbAbBbCbDbEbFQ1VQ1YQ0ZQ0[Q0\Q0]Q1ZQ0WQ1[Q1]Q1_Q11Q1`Q0~Q1bQ0nQ1cQ1dQ1eQ1iQ1jQ0{Q1lQ1mQ1nQ0vP_PoP^P5PkP5PxP>PyPzAI{|}Q1:Q1;b:b;b<%0ER}P3b9b8b7b6b5b4b3b1bIbJbKbAbBbCbDbEbFI0HJ0GH0FQ1W,kpQ05#GS05Q001F421k46Rk[S0v1k241F64S1n[S1m1F=6\kB0E423S1lP3n2001000000120000000UXS5XR5Q05Q1m[^S5^R5P3P0PpQ0SQ0Y1<CES0Y%9pS0S\}\WS0{A;CE2VYX0XS1j%0pS1i\Y^0XS1eQ0ZQ0[Q0\Q0]Q0b,<C%0\%9b[\WQ0|=;C2VYX0X%0`\Y^0XQ0i,<CQ0k#0Q0p,1ES0k,LC[\W11EcS0i=;C2VYX0XQ0i,KC\Y^0XQ0q,<CQ0s#0Q0x#9[\W11GlS0x=;C2VYX0XQ0x,KC\Y^0XAxpjQ1Ep3Rj,7mX=5,y5Q01P517rjX=5%2pS0s#GS0qP3Q17/7jS0bQ0o,NwQ0o#2#Gf]R\A4CInR}1:\}15\}CC[1R\}%9}15uMRk?UkM[1OuM%XMA4CItRtf_Rk/5tS1dQ1d3V[1Wkt%2tf`R^A4CIvRv':#2[1Z^v%2vS1cfaRoA4CIwRw'5S0n/7o[1:owS1bP5fbR_A4CI\RZ'5S0~P5PxP>PyPzQ18Q04$076065=A{|,q{Q1:Q1;b:b;b<Q0sQ1Q[P3b9S04b8b7b@b6b5b4b3W1XT5P2P3O2n2001000000121100000bPbIbJbKbAbBbCbDbEbFbXbYPpQ0RP0P2Q05Q00Q0vQ1mQ1n1k6=[Q1lP2n2001000000120000000UXS5XR5S1lQ05Q0v[^S5^R5S05P3P[Q0UQ0T$0DQ0T#0Q0X#9[Q0X,_V%0VQ0_#0Q0pQ1\'5#0[[Q0YQ0{Q1jQ1eQ0ZQ0[Q0\Q0]Q0},<CS0}Q0|#0%9e[\WS0|Q0y=;C2VYX0XS0_%0g\Y^0XS0XQ0k,<CS0kQ0i#011EiS0i,LC[\WS0U11ElS0v=;C2VYX0XS1nQ0v,KC\Y^0XS1mQ0u,<CS0uQ0x#011GqS0x,LC[\WS0011GdS1`=;C2VYX0XS11Q1`,KC\Y^0XS1_Q0F9xprS0FQ15/7jX=5,y5S15Q01P5Q0bX=5S0bQ17#2#GP317}jS1]1NuM%2M#GPkPt1:ktQ1dCC[1Rkt%9t15^vRM?UMv[1O^v%XvQ0nQ0n5Vw[1Wow%2w1:_Z#2[1Z_Z%2ZfcRMA4CIuR}'5S1d/7M[1:M}P5fdRrA4CIkS1['5P5PxP>%h4?@2yPzP{P{Q1I/T;9I{|S1IP~Aa{|1P~P{P{Q14/o;P~P{AI{|;S141n{=5P{P~AA{1|,q{CmDYFHQ1:Q1;b:b;b<X25X?5X>sQ0>#0%92[13U4Q0@/?=%26Q1Q[[[[^25^?5^>sP313oAPoA4CIoRgQ0OP0P\O6b9b8b7bUb@b6b5b4W3XT5P2P3O2n2001000000121100000bPbIbJbKbAbBbCbDbEbFbXbYb1PHO4b1I0CO4b1Q0a/FpQ1lQ05P3P[PpQ0=Q12Q0YQ0{Q1jQ1eQ0ZQ0[Q0\Q0]1_ip%0iS0]Q1i15qp#0[[Q0}Q0|Q0_Q0XQ0kQ0UQ1nQ1mQ0uQ00Q11Q1_Q0FQ15Q01P5Q0bQ0qP3Q1]1NupQ0qPkPp1:kp15kpCC[1RkpQ0S15^pRu?Uup[1O^p%Xp15opRu=Vpu[1WopQ0s1:_p#2[1Z_pQ0s15Mp/7M[1:MpP515rpP5feRuA4CI^R\'N%2\#GffR0Pg1:0g150gS0sCC[1R0g%9gfgS0SA4CI_Rg'5S0qQ0q;Ug[Q0S/Og%XgA4CIMRgfhS0q/5gS0bQ0b3V[Q0q/Wg%2gfiS0bA4CIrS15':#2[Q0bQ15'ZQ15#2fjS15A4CIuS0b'5Q15'7[Q15Q0b':P5fkA4CI0'5P5Q04c09bebgblbkbjbib8b7bUb@b6b5b4W3XT5P2P3O2n2001000000121100000bPbAbBbCbDbEbFbXbYbzb{b|b}P2O41kp[Q01P5Q1S,7aX=5Q1QP3Q1S,7c1_i]Q0]%0bQ1h#0[[Q0YQ0{Q1jQ1eQ0w,<CQ0y#0Q0r[\WQ10=;C2VYX0X%0m\Y^0XQ0i,<CQ0v#011Eq,LC[\W11EdR[=;C2VYX0X1KC[\Y^0XQ0x,<CQ1`#011Gf,LC[\W11GhR[=;C2VYX0X1KC[\Y^0XQ17Q0I5xpQ0o/7jX=5,y5Q01P5Q1]X=5Q1QP317tj1N^vQ1c#GPoPwQ1bQ0nCC[1Row%9wQ0~Q0~;UZ[1O_Z%XZQ1dQ1d5V}[1WM}%2}Q1[,:r#2[Q1[,ZrQ1[#215u\/7u[1:u\P5Q0sP5Q0mQ0`#DR\#D#J5s5RuQ0hQ0j'f'\RrQ0f#JR}Q0h'fQ0:#>RZ#>$03#u#uR_#>Rw#>$03#B,z5Q0l-045Ro'e&00Z,~5Q0e#J5s5%BZRZ,z5RvQ0h'eQ1<,ev3t'\+0BRv?^vx7^rP>%hPRr?@=y9@y4Q1>?@6yQ1@7@P7@2PzP{Q1DP~P{P{Q1AP~P{Q1B#>#[Rv/}|DrP~P{P{Q1FP~Q1NQ1G5P{P~P{P{Q1HP~Al5DvQ1C'T9A{;P~P{Q1KP~P{Q08#c#[Rv%MZ5l59A{;P~P{Q16P~P{%B_R_#MR^-02;-0A{P~P{P{Q02#[Rt%MNRj,T^'pP~P{P{%MLRp9{5;/ptP~P{Q07P~P{Q1LP~P{Q1MQ1O5P{P~1n{HR;CmFQDYDYFQFQFHFHFQQ1:Q1;b:b;b<X25X?5XL5XM5XN5XO5XQ5X>sXGsXHsQ0A1764[Q0BQ0H[Q1PA|J@P[Q1RP@PBPJP?CC[Q0C1EJZ,7?13U?1SB_11_N,8HQ0?/8QQ0DQ0E#21vQOP:[[[[[[[[[[[[[^25^?5^L5^M5^N5^O5^Q5^>s^Gs^HsP3Q1Q13MAQ0<P4PSPgQ0SP2Q0qPMP6P=P?PPQ0KP:PVPaPlPqPdPfPkOGb9b8beb@b6b5b4b3W1XT5P2P3O2n2001000000121100000bPbIbJbKbAbBbCbDbEbFWxX75P2P3O2n2001000000121100000b`b1b`bPbr+05WpP3O1n200110100021010<1110;bfQ0N1=SL,ECRk00L:1gk:Rf/7:9jk:13:k17fk'?+01Q0O/=L,EC/gSP5A4CIO,_T%0TQ1W#0Q0aQ0M'5#0[[Q1X,<CQ0P#0Q0R#9[\WQ0T=;C2VYX0XQ0V\Y^0XQ0Q,<CQ0O,1E#011ET,LC[\WQ1^=;C2VYX0XQ1^,KC\Y^0X11GT,<CQ0^,1G#0Q0a,1G,LC[\WQ1a=;C2VYX0XQ1a,KC\Y^0XQ0pQ1\'NQ1\#2#GPcQ0cQ0c,:cQ0c,5cCC[Q0c,RcQ0d15i]Rc?Uc][1Oi]%X]15lbR]=Vb][1WlbQ1fQ1g#2[1Zq`%2`Q1k/7d[1:deP5Q0zP5Q03$00,~5%J\5s5Q0g#JR\1z5CReQ1='e;to'\RdQ1<Q1=/fo5t\,\uRuQ0h,ee/fo,\\R`Q1<,ee=t\o,\}R}A^`}x3^9^du3^P>Q1>?@PyQ1?7@4A@rPyQ1@7@67@2PzP{P{Q1EP~AA{t<P~P{P{Q1EP~AA{v|P~P{P{Q099a{|RzP~Q1NQ099a{t5P{P~P{P{Q1E,q{P~Q09=l5v/Tt9A{<P~P{P{Q19P~P{Q1IP~PzCmP~P{P{P7P8P8P9Q18A{5<pRp5l5R9=a{DAA{1D5P{Q1OAA{195P{K0@P~P{AI{<^P~P{P{1Tpj,oDP~P{P{Q13/o<P~P{P{1}t|P~P{Q14=P{;P~P{%BwRw#M,p1DrDYDYDYFQFHFHFHFHFHQ1:Q1;b:b;b<X25X?5XL5XM5XN5XO5XQ5X>sXGsXHsQ0B17=6[%2?Q0H[%9PA|J?B[Q0HQ1Q[P?PFPJPPCC[11I?#0%9H[\WQ0;17@F7jFQ0EQ0;,7@'?+0113B_1=FL/1N,3H13KJ%2QQ0L,vH18Hw[[[[[[[[[[[^25^?5^L5^M5^N5^O5^Q5^>s^Gs^HsP313lA1=nL,EC,3hQ0<P4PmPhP2PnPlQ0GP6P=P?PPQ0EQ0IQ0JQ0KPRP:PaOEb9b8b7b6b5b4b3b1b~c02c03c04c05c06c07c0:bhbnWyWwWoWmWvWtP2P3O2n2001000000121000000W1WuP2P3O2n2001000000121000000W1WqP2P3O2n2001000000121000000W1Xc5P2P3O2n2001000000121100000W1Xd5Xb5P2P3O2Xd5Xb5o"). Qed.

End PM.
