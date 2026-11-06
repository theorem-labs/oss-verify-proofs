(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:1527-1530
   [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan build (lib/B). The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACes.v:251-253 [Apache-2.0]. The [Apache-2.0 OR MIT] text is used under
   Apache-2.0. *)
(* +0x1910 .. +0x1988 (0x82084 .. 0x820fc) of LLVMFuzzerTestOneInput's build-B walk (fuzz_identity.asan-ubsan):
   the last piece of segment J, j_fits_stmt of lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_pre.v. x19 = the
   display's length (0x82084), the two UBSan bound tests (0x8208c, 0x82090), the NUL of exp_dp (0x82098), the
   name test (0x820a0), the memchr of the first dash in exp_nm (0x820b0), the token test (0x820c4), the display
   test and reac_box_name's answer (0x820c8 .. 0x820f0), and the re-poisoning of w4's shadow cell (0x820f8). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_seg_J_loops_stmt.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require LLVMFuzzerTestOneInput_seg_J_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require put_dec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrlenDef StrcmpDef MemchrDef SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import LLVMFuzzerTestOneInput_seg_J_pre.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import WrapRo.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* The symbolic state at 0x82084. Region 0: the three capacities the piece loads, base s1 (atom 9), read-only:
   mf+120 = cap_disp (atom 34), mf+128 = cap_tok (atom 33), mf+144 = cap_name (atom 32). Region 1: the NUL byte
   of exp_dp, base x12 = &exp_dp + (its length - 5) (atom 12), offset 5. Region 2: w4's shadow cell, base the
   frame's shadow (atom 23), offset 86. x11 is pinned to 5, so x19 = x13 + 5 and the NUL's address is x12 + 5. *)
Definition jf_r0 : YP09.region := YP09.mkRegion (Some 9%nat) 120 152 120 120
[YP09.mkChunk 120 (CVal 8 (SOff 34 0)); YP09.mkChunk 128 (CVal 8 (SOff 33 0));
YP09.mkChunk 144 (CVal 8 (SOff 32 0))].
Definition jf_r1 : YP09.region := YP09.mkRegion (Some 12%nat) 5 6 5 6 [].
Definition jf_r2 : YP09.region := YP09.mkRegion (Some 23%nat) 86 87 86 87 [].
Definition jf_ss0 : sstate := mkSS 0x1910 sr_atoms [jf_r0; jf_r1; jf_r2] None (mkFacts [] [] []).
Definition jf_ss : sstate :=
mkSS 0x1910 (sr_set sr_atoms 11%bv (SLit 5)) [jf_r0; jf_r1; jf_r2] None (mkFacts [] [] []).

Lemma jf_bvu : forall (w : word) z, w = Z_to_bv 64 z -> bv_unsigned w = z mod 2 ^ 64.
Proof. intros w z ->. rewrite Z_to_bv_unsigned. reflexivity. Qed.
Lemma jf_U_offu : forall E n c v, bv_unsigned (ew E n) = v -> 0 <= v + c < 2 ^ 64 -> U E (SOff n c) = v + c.
Proof. intros E n c v H Hv. rewrite U_SOff, H. apply zcanon_id. unfold M64. exact Hv. Qed.

(* The token's length: TOK drops the first dash and keeps every other byte. *)
Lemma jf_tok_true : forall l, length (SlotModel.tok_go true l) = length l.
Proof.
induction l as [|b r IH]; [reflexivity|]. cbn [SlotModel.tok_go negb andb length]. rewrite IH. reflexivity.
Qed.
Lemma jf_tok_false : forall l, Z.of_nat (length (SlotModel.tok_go false l)) =
Z.of_nat (length l) - (if SlotModel.has_dash l then 1 else 0).
Proof.
unfold SlotModel.has_dash. induction l as [|b r IH]; [reflexivity|].
cbn [SlotModel.tok_go existsb negb andb].
destruct (RcIdentModel.bz b =? 45); cbn [orb length].
- rewrite jf_tok_true. lia.
- rewrite Nat2Z.inj_succ, IH. destruct (existsb _ r); lia.
Qed.
Lemma jf_tk_len : forall inp, Z.of_nat (length (SlotModel.n_TK inp)) = SlotModel.n_lt inp.
Proof. intro inp. unfold SlotModel.n_TK, SlotModel.TOK. rewrite jf_tok_false. reflexivity. Qed.

(* The token length the code computes at 0x820b4 / 0x820b8: n_ln minus one when memchr found a dash. *)
Lemma jf_utl : forall nl q, 1 <= nl <= 21 -> 0 <= q < 2 ^ 63 ->
zcanon (zalu_raw 63 64 ALU_SUB (zcanon nl) (zcanon (zalu_raw 63 64 ALU_SLTU (zcanon 0) (zcanon q)))) =
nl - (if 0 <? q then 1 else 0).
Proof.
intros nl q Hn Hq. cbn [zalu_raw].
rewrite (zcanon_id 0), (zcanon_id q), (zcanon_id nl) by (unfold M64; lia).
destruct (0 <? q); cbv iota.
- rewrite (zcanon_id 1) by (unfold M64; lia). apply zcanon_id. unfold M64. lia.
- rewrite (zcanon_id 0) by (unfold M64; lia). apply zcanon_id. unfold M64. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).

Lemma jf_aview_bytes : forall (W : world SEGS) m a bs j, bytes_at8 W m a bs -> (j < length bs)%nat ->
aview SEGS (w_H W) m (a + Z.of_nat j) = Some (bv_unsigned (nth j bs (Z_to_bv 8 0))).
Proof.
intros W m a bs j H Hj. unfold bytes_at8 in H.
destruct (H j ltac:(rewrite length_map; exact Hj)) as [Hv _].
specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
unfold aview. rewrite Hv. cbn [option_map]. f_equal.
replace (nth j (map (fun b : byte => bv_unsigned b) bs) 0) with (bv_unsigned (nth j bs (Z_to_bv 8 0)))
by (rewrite <- (map_nth (fun b : byte => bv_unsigned b) bs (Z_to_bv 8 0) j); reflexivity).
pose proof (bv_unsigned_in_range 8 (nth j bs (Z_to_bv 8 0))) as Hr. change (bv_modulus 8) with 256 in Hr.
rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (bv_modulus 8) with 256. change (2 ^ 8) with 256.
rewrite !(Z.mod_small (bv_unsigned (nth j bs (Z_to_bv 8 0))) 256) by lia. reflexivity.
Qed.

(* The first byte equal to c is the model's index when the bytes before it differ from c and it is c. *)
Lemma jf_first_byte_eq : forall (W : world SEGS) m x n c kk k0,
first_byte SEGS W m x n c kk -> 0 <= k0 <= n ->
(forall j, 0 <= j < k0 -> exists b, aview SEGS (w_H W) m (x + j) = Some b /\ b <> c) ->
(k0 < n -> aview SEGS (w_H W) m (x + k0) = Some c) -> kk = k0.
Proof.
intros W m x n c kk k0 (Hk & Hlt & Hat) Hk0 Hb Hw.
destruct (Z.lt_trichotomy kk k0) as [H | [H | H]]; [exfalso | exact H | exfalso].
- destruct (Hb kk ltac:(lia)) as (b & Eb & Nb). rewrite (Hat ltac:(lia)) in Eb. injection Eb as Eb.
  exact (Nb (eq_sym Eb)).
- destruct (Hlt k0 ltac:(lia)) as (b & Eb & Nb). rewrite (Hw ltac:(lia)) in Eb. injection Eb as Eb.
  exact (Nb (eq_sym Eb)).
Qed.

(* The piece's write windows: the NUL byte in the entry's frame and w4's shadow cell in the frame's shadow. *)
Lemma jf_awr : forall (g : ectx) pos E cs0 cs1 cs2 STK sp0 FP bl0 blc ly2 nul,
frame_addr ly2 4 pos = SFa g pos ->
bv_unsigned (ew E 12) + 5 = nul -> SFa g pos <= nul < SFa g pos + 1024 ->
bv_unsigned (ew E 23) = shadow_addr (SFa g pos) ->
awr_ok E [YP09.mkRegion (Some 9%nat) 120 152 120 120 cs0; YP09.mkRegion (Some 12%nat) 5 6 5 6 cs1;
YP09.mkRegion (Some 23%nat) 86 87 86 87 cs2] STK sp0 FP bl0 blc ly2 [(4, pos)].
Proof.
intros g pos E cs0 cs1 cs2 STK sp0 FP bl0 blc ly2 nul EFa H12 Hn H23.
apply awr_ok_cons_ro; [cbn; lia|].
apply (awr_ok_cons_gen E _ _ STK sp0 FP bl0 blc ly2 [(4, pos)] 12%nat (bv_unsigned (ew E 12)));
[reflexivity | reflexivity | |].
{ intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists 4, pos.
  split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite EFa.
  change (fs_frame_bytes 4) with 1024. lia. }
apply (awr_ok_cons_gen E _ _ STK sp0 FP bl0 blc ly2 [(4, pos)] 23%nat (shadow_addr (SFa g pos)));
[reflexivity | exact H23 | |].
{ intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists 4, pos.
  split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite EFa.
  change (fs_frame_bytes 4 / 8) with 128. lia. }
apply awr_ok_nil.
Qed.

(* A run keeps every byte outside its write windows: outside the NUL byte, w4's shadow cell and the memchr
   window below sp = mf, memory is the memory the piece started with. *)
Lemma jf_keep_step : forall (W : world SEGS) E cs0 cs1 cs2 (m0 m m' : word -> option byte) mf nul shc,
bv_unsigned (ew E 9) = mf -> bv_unsigned (ew E 12) + 5 = nul -> bv_unsigned (ew E 23) + 86 = shc ->
frame_of E [YP09.mkRegion (Some 9%nat) 120 152 120 120 cs0; YP09.mkRegion (Some 12%nat) 5 6 5 6 cs1;
YP09.mkRegion (Some 23%nat) 86 87 86 87 cs2] (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 4096 <= a < mf) -> a <> nul -> a <> shc ->
aview SEGS (w_H W) m a = aview SEGS (w_H W) m0 a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 4096 <= a < mf) -> a <> nul -> a <> shc ->
aview SEGS (w_H W) m' a = aview SEGS (w_H W) m0 a).
Proof.
intros W E cs0 cs1 cs2 m0 m m' mf nul shc H9 H12 H23 HF HK a Ha H1 H2 H3.
rewrite <- (HK a Ha H1 H2 H3).
apply (@kept_of_frame SEGS E _ (w_H W) m m' (fun x => x = nul \/ x = shc) HF);
[| exact Ha | intros [E1 | E1]; [exact (H2 E1) | exact (H3 E1)]].
intros b wlo whi x Hin Hx. cbn [windows map In] in Hin.
destruct Hin as [Eq | [Eq | [Eq | []]]]; injection Eq as <- <- <-; cbn [base_val] in Hx.
- lia.
- left. lia.
- right. lia.
Qed.

Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
#[local] Notation JKEEP := (jkeep B).
#[local] Notation INVJ := (inv_J_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
Variable G : list (Z * Z).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
(* The contract's HRO (lib/B/Prog/LLVMFuzzerTestOneInput.v:189): memchr's read-only premise at 0x820b0. *)
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.

(* The memchr wrapper (lib/B/Rt/MemchrDef.v amemchr_realizes) at a slot of a journal: the journal goes on
   through the call (it writes only the ESTACK window below sp), as seg_D4's d4_memchr_at. *)
Lemma jf_memchr_at : AR_laws SEGS B -> amemchr_realizes SEGS B (SIGMA IB___interceptor_trampoline_memchr) ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x c n (o : Z) raw,
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 c -> getr regsT 12 = w64 n ->
0 <= c < 256 -> 0 <= n < 2 ^ 32 -> 0 < x -> x + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
src_ok SEGS W regsT memT x n -> amem_range x n ->
range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x n ->
(0 < n -> shadow_hull_vis (aview SEGS (w_H W) memT) x n) ->
aro_unowned SEGS B (aview SEGS (w_H W) memT) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA IB___interceptor_trampoline_memchr)) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\
(exists kk, first_byte SEGS W memT x n c kk /\ getr regs2 10 = (if kk <? n then w64 (x + kk) else w64 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
m_fds md2 = m_fds mdc /\ m_fs md2 = m_fs mdc).
Proof.
intros LAWS AMEMCHR W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x c n o raw
HJ Ha0 Ha1 Ha2 Hc Hn Hx Hxn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hmx Hrx Hhx Hro.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ apply (ecall_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o HJ Hsp' Hal Hneg Hbud);
  [rewrite Hra; exact Hraw | exact Hgp | exact Htp]. }
eapply SRr_mono.
{ exact (AMEMCHR lyc Sc W regsT memT mdc x c n HPRE Ha0 Ha1 Ha2 Hc Hn Hx Hxn Hsx Hmx Hrx Hhx Hro). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; f_equal; f_equal; apply Z_to_bv_bv_unsigned|].
split.
{ eapply (ajournal_after_write SEGS B LAWS pa_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
  (fun a => spZ regsT - ESTACK <= a < spZ regsT) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha). exact Hna.
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha; left; left; rewrite Hsp' in Ha; lia.
  - exact HAR2.
  - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr|]. split; [exact Hpres2|].
pose proof Hsame as Hs'. unfold same_but_materialized in Hs'. rewrite Hs'.
split; [apply j_wvb_fds | apply j_wvb_fs].
Qed.

(* The cut at +0x1988 from the start cut's facts and the final state: the registers the piece keeps, x22 =
   cap_disp, memory equal to the start's outside the NUL byte, w4's shadow cell and the memchr window, and the
   NUL itself. *)
Lemma jf_post : AR_laws SEGS B -> STK_LLVMF <= LLVMF_STK ->
forall (g : ectx) pos mf nm tk dp ly2 S2 (W2 : world SEGS) regs2 mem2 md2 regs' mem' md',
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly2 S2 W2 mem' md' (4 * Z.of_nat (m_nrec g) + 7) ->
frames S2 = [(4, pos)] ->
0 <= 4 * Z.of_nat (m_nrec g) + 7 <= EV_LLVMF ->
mo_le MT (e_S g) S2 ((4 * Z.of_nat (m_nrec g) + 7) * MEV MT) ->
mo_ok MT S2 ((EV_LLVMF - (4 * Z.of_nat (m_nrec g) + 7)) * MEV MT) ->
ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
JKEEP g pos mf nm tk dp ly2 S2 W2 regs2 mem2 ->
jdp_regs g pos regs2 -> jdp_mem g pos W2 mem2 (SlotModel.n_EXP_DP (e_pl g)) ->
bytes_at8 W2 mem2 (SFa g pos + V_nm) (SlotModel.n_EXP_NM (e_pl g) ++ [RcIdentModel.zb 0]) ->
SlotModel.n_wok (e_pl g) = true ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 4096 <= a < mf) -> a <> SFa g pos + 592 + SlotModel.n_ld (e_pl g) ->
a <> shadow_addr (SFa g pos) + 86 -> aview SEGS (w_H W2) mem' a = aview SEGS (w_H W2) mem2 a) ->
val_mem SEGS (rd W2 mem') (SFa g pos + 592 + SlotModel.n_ld (e_pl g)) 1 0 ->
(forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv] -> getr regs' r = getr regs2 r) ->
getr regs' 22 = w64 (SlotModel.t_cap_disp (e_pl g)) ->
m_fds md' = m_fds md2 -> m_fs md' = m_fs md2 ->
INVJ g pos mf nm tk dp W2 (cfg_at SEGS (BASE + 0x1988) regs' mem' md').
Proof.
intros LAWS HSTK g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regs' mem' md'
HJ Hfrs Hk MLE MOK HC HK HDR HDM HNM Hwok KEEP HNUL RK R22 Efds Efs.
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
V24 & V32 & V40 & V48 & V56 & V64b & V72 & V80 & V88 & V96 & V104 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct HK as (Hbl & Rs7 & R24 & R21 & V152 & V184 & V144 & V128 & V120 & V176 & V160 & V112 & _ & Hbufs).
destruct HDR as (_ & _ & R25 & R26).
destruct HDM as (Hznm & Hzdp & Hdp).
unfold V_nm, V_dp, N_nm, N_dp in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
destruct (j_geo B LLVMF_STK LAWS g pos _ ly2 S2 W2 mem' md' HJ Hfrs)
as (EFa & HSF0 & HSF1 & HSF64 & Hsh0 & Hsh1 & Hsfsh).
assert (Has : ASTACK = 16384) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
assert (Esh : shadow_addr (SFa g pos) = SHADOW_OFF + SFa g pos / 8) by reflexivity.
pose proof (LLVMFuzzerTestOneInput_seg_J_model.m2_n_ld_le (e_pl g) Hwok) as Hnld.
pose proof (LLVMFuzzerTestOneInput_seg_J_model.m1_n_ln_le (e_pl g) Hwok) as Hnln.
pose proof (LLVMFuzzerTestOneInput_seg_J_model.m2_caps (e_pl g)) as Hcaps.
(* the transports *)
assert (VMS : forall a (n : nat) v, mf <= a -> a + Z.of_nat n <= e_sp0 g ->
val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 mem') a n v).
{ intros a n v H1 H2 Hv. apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 mem' a a n v); [|exact Hv].
  intros kk Hkk. apply KEEP; clear - H1 H2 Hkk Hmf0 Hmfb H47 Hshi HSF0 HSF1 Hsh1 C1 Hnld; lia. }
assert (VMF : forall o (n : nat) v, 0 <= o -> o + Z.of_nat n <= 1024 ->
(o + Z.of_nat n <= 592 + SlotModel.n_ld (e_pl g) \/ 592 + SlotModel.n_ld (e_pl g) < o) ->
val_mem SEGS (rd W2 mem2) (SFa g pos + o) n v -> val_mem SEGS (rd W2 mem') (SFa g pos + o) n v).
{ intros o n v H1 H2 H3 Hv. apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 mem' (SFa g pos + o) (SFa g pos + o) n v); [|exact Hv].
  intros kk Hkk. apply KEEP; clear - H1 H2 H3 Hkk Hmf0 HSF0 HSF1 Hsh1 Hsfsh C1 Hnld; lia. }
assert (GAF : forall o l, 0 <= o -> o + Z.of_nat (length l) <= 1024 ->
(o + Z.of_nat (length l) <= 592 + SlotModel.n_ld (e_pl g) \/ 592 + SlotModel.n_ld (e_pl g) < o) ->
garr8 SEGS (rd W2 mem2) (SFa g pos + o) l -> garr8 SEGS (rd W2 mem') (SFa g pos + o) l).
{ intros o l H1 H2 H3 Hg. apply (j_garr8_moved SEGS (w_H W2) (w_H W2) mem2 mem' (SFa g pos + o) l); [|exact Hg].
  intros kk Hkk. apply KEEP; clear - H1 H2 H3 Hkk Hmf0 HSF0 HSF1 Hsh1 Hsfsh C1 Hnld; lia. }
assert (SHZ : forall o n, 0 <= o -> o mod 8 = 0 -> 0 <= n -> o + n <= 688 ->
sh_zero W2 mem2 (SFa g pos + o) n -> sh_zero W2 mem' (SFa g pos + o) n).
{ intros o n H1 H2 H3 H4 Hz. unfold sh_zero in *.
  apply (j_zero_shadow_moved (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W2) mem') SHADOW_OFF (SFa g pos + o) n); [|exact Hz].
  intros i Hi. apply KEEP; clear - H1 H2 H3 H4 Hi Hmf0 HSF0 HSF1 HSF64 Hsh1 Hsfsh C1 Esh Hnld;
  unfold shadow_of_addr; rewrite Esh in *; unfold SHADOW_OFF in *; lia. }
assert (GAH : forall b m a l, In (b, m) (ablocks B ly2 S2) -> b <= a -> a + Z.of_nat (length l) <= b + req_size m ->
garr8 SEGS (rd W2 mem2) a l -> garr8 SEGS (rd W2 mem') a l).
{ intros b m a l Hin H1 H2 Hg.
  destruct (al_blocks SEGS B LAWS ly2 S2 W2 mem' md' b m HAR Hin) as (_ & H4096 & Hceilb & Happ & _).
  pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem' md' b m 4 pos HAR Hin ltac:(rewrite Hfrs; left; reflexivity))
  as Hsep.
  rewrite EFa in Hsep. change (fs_frame_bytes 4) with 1024 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
  apply (j_garr8_moved SEGS (w_H W2) (w_H W2) mem2 mem' a l); [|exact Hg].
  intros kk Hkk. apply KEEP; clear - H1 H2 Hkk H4096 Hceilb Happ Hsep Hmf0 HSF0 HSF1 Hsh1 Esh C1 Hnld;
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *; rewrite ?Esh; lia. }
(* the input block *)
assert (HINB : bytes_at8 W2 mem' (e_p g) (e_pl g)).
{ pose proof HPRE as (_ & _ & _ & _ & Hinp & Hlen & _).
  destruct Hinp as [[Hne Hpe] | [[Hnp Hn26] Hine]].
  - unfold bytes_at8. intros j Hj. rewrite length_map in Hj. exfalso. clear - Hj Hne Hlen. lia.
  - assert (Hpn2 : In (e_p g, e_n g) (ablocks B ly2 S2)).
    { destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right.
      exact Hine. }
    pose proof (req_size_pos (e_n g) ltac:(lia)) as Hrq.
    unfold bytes_at8 in *. apply (GAH (e_p g) (e_n g) (e_p g)); [exact Hpn2 | lia | | exact Hinb].
    rewrite length_map, <- Hlen. clear - Hrq. lia. }
unfold inv_J_end, acut. unfold V_nm, V_dp, N_nm, N_dp.
exists ly2, S2, regs', mem', md'.
split; [reflexivity|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
split; [exact MLE|]. split; [exact MOK|].
split.
{ unfold ecommon.
  split; [rewrite (RK 2%bv ltac:(cbn; tauto)); exact Rsp|].
  split; [rewrite (RK 9%bv ltac:(cbn; tauto)); exact Rs1|].
  split; [rewrite (RK 8%bv ltac:(cbn; tauto)); exact Rs0|].
  split; [exact Hmfb|]. split; [exact Hmf32|].
  split; [rewrite (RK 3%bv ltac:(cbn; tauto)); exact Rgp|].
  split; [rewrite (RK 4%bv ltac:(cbn; tauto)); exact Rtp|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V16]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V64]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V192]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V168]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact Vra]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact Vs0]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V24]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V32]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V40]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V48]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V56]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V64b]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V72]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V80]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V88]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V96]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V104]|].
  split; [apply VMF; [lia | cbn; lia | right; clear - Hnld; lia | exact Vflag]|].
  split; [exact HPRE|].
  split; [intros fd; rewrite Efds; exact (Hfds fd)|].
  split; [rewrite Efs; exact Hfs | exact HINB]. }
split; [exact Hbl|].
split; [unfold sh_reg in *; rewrite (RK 23%bv ltac:(cbn; tauto)); exact Rs7|].
split; [rewrite (RK 24%bv ltac:(cbn; tauto)); exact R24|].
split; [rewrite (RK 21%bv ltac:(cbn; tauto)); exact R21|].
split; [exact R22|].
split; [rewrite (RK 25%bv ltac:(cbn; tauto)); exact R25|].
split; [rewrite (RK 26%bv ltac:(cbn; tauto)); exact R26|].
split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V152]|].
split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V184]|].
split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V144]|].
split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V128]|].
split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V120]|].
split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V176]|].
split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V160]|].
split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V112]|].
split; [apply SHZ; [lia | reflexivity | lia | lia | exact Hznm]|].
split; [apply SHZ; [lia | reflexivity | lia | lia | exact Hzdp]|].
split.
{ intros _. split.
  - unfold bytes_at8 in *. apply GAF; [lia | | | exact HNM].
    + rewrite length_map, length_app. cbn [length]. unfold SlotModel.n_ln in Hnln. clear - Hnln. lia.
    + left. rewrite length_map, length_app. cbn [length]. unfold SlotModel.n_ln in Hnln. clear - Hnln Hnld. lia.
  - unfold bytes_at8 in *. rewrite map_app. apply garr8_app. split.
    + apply GAF; [lia | | | exact Hdp].
      * rewrite length_map. unfold SlotModel.n_ld in Hnld. clear - Hnld. lia.
      * left. rewrite length_map. unfold SlotModel.n_ld. clear. lia.
    + intros j Hj. cbn [length map] in Hj. destruct j as [|j]; [|clear - Hj; lia].
      cbn [nth map]. split; [|change (bv_unsigned (RcIdentModel.zb 0)) with 0; lia].
      change (bv_unsigned (RcIdentModel.zb 0)) with 0.
      replace (SFa g pos + 592 + Z.of_nat (length (map (fun b : byte => bv_unsigned b) (SlotModel.n_EXP_DP (e_pl g))))
        + Z.of_nat 0) with (SFa g pos + 592 + SlotModel.n_ld (e_pl g))
      by (rewrite length_map; unfold SlotModel.n_ld; clear; lia).
      exact HNUL. }
intros Hr0. destruct (Hbufs Hr0) as (Bnm & Btk & Bdp).
destruct (LLVMFuzzerTestOneInput_seg_J_model.m2_fits_r0 (e_pl g) Hr0) as (_ & Hfn & Hft & Hfd).
assert (INB : forall h, In h [(nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1);
  (tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1); (dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1)] ->
  In h (ablocks B ly2 S2)).
{ intros h Hh. destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app.
  left. exact Hh. }
pose proof (req_size_pos (Z.max (SlotModel.t_cap_name (e_pl g)) 1) ltac:(lia)) as Q1.
pose proof (req_size_pos (Z.max (SlotModel.t_cap_tok (e_pl g)) 1) ltac:(lia)) as Q2.
pose proof (req_size_pos (Z.max (SlotModel.t_cap_disp (e_pl g)) 1) ltac:(lia)) as Q3.
pose proof (jf_tk_len (e_pl g)) as Ltk.
unfold bytes_at8 in *.
split; [|split].
- apply (GAH nm (Z.max (SlotModel.t_cap_name (e_pl g)) 1) nm); [apply INB; left; reflexivity | lia | | exact Bnm].
  rewrite length_map, length_app. cbn [length]. unfold SlotModel.n_ln in Hfn. clear - Hfn Q1. lia.
- apply (GAH tk (Z.max (SlotModel.t_cap_tok (e_pl g)) 1) tk); [apply INB; right; left; reflexivity | lia | |
  exact Btk].
  rewrite length_map, length_app. cbn [length]. clear - Hft Q2 Ltk. lia.
- apply (GAH dp (Z.max (SlotModel.t_cap_disp (e_pl g)) 1) dp); [apply INB; right; right; left; reflexivity | lia | |
  exact Bdp].
  rewrite length_map, length_app. cbn [length]. unfold SlotModel.n_ld in Hfd. clear - Hfd Q3. lia.
Qed.

Ltac jf_awr_tac := eapply jf_awr; [eassumption | eassumption | eassumption | eassumption].
Ltac jf_keep_tac W2 mem2 KEEP :=
  lazymatch goal with HFr : frame_of ?E _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    let K2 := fresh "K" in
    pose proof (jf_keep_step W2 E _ _ _ mem2 _ _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)
      HFr KEEP) as K2;
    clear KEEP; rename K2 into KEEP
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* prreg without its context-wide lia (the havoc side conditions are closed after a clear). *)
Ltac jf_prreg HS r Hq :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hq;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hq;
    cbn [ms_regs restrict mkst sv_denot] in Hq;
    repeat (rewrite ew_havoc_old in Hq by (clear; lia));
    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hq
  end.
Ltac jf_rk_tac HS EE :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [In] in Hr;
  repeat (destruct Hr as [Hr | Hr];
    [ subst r; lazymatch goal with |- getr _ ?x = _ =>
        let Hq := fresh "Hq" in jf_prreg HS x Hq; rewrite Hq; apply EE; reflexivity end | ]);
  destruct Hr.
Ltac jf_fds := repeat rewrite j_wvb_fds; first [reflexivity | assumption].
Ltac jf_fs := repeat rewrite j_wvb_fs; first [reflexivity | assumption].
Ltac jf_end HS EE E34 :=
  apply SRr_ret; pmkst HS;
  lazymatch type of HS with st_ok_pi _ _ ?E ?ss (restrict _ ?ms) =>
  lazymatch type of EE with forall n r, _ -> ew _ n = getr ?regs2 r =>
    let rr := eval vm_compute in (nth_error (ss_mem ss) 1) in
    lazymatch rr with Some ?r1 =>
      let HR1 := fresh "HR1" in
      pose proof (st_ok_pi_region_nth E ss _ 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1;
      let HNUL := fresh "HNUL" in
      pose proof (@field_of_region SEGS E _ 12%nat _ _ 5 6 5 6 5 1%N (SLit 0) 0 HR1 eq_refl
        ltac:(left; reflexivity) eq_refl ltac:(clear; cbn; lia) ltac:(clear; cbn; lia)) as HNUL;
      change (N.to_nat 1) with 1%nat in HNUL; cbn [ms_mem restrict] in HNUL;
      lazymatch goal with Hu : bv_unsigned (ew E 12) + 5 = _ |- _ => rewrite Hu in HNUL end;
      let RK := fresh "RK" in
      assert (RK : forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv] ->
        getr (ms_regs ms) r = getr regs2 r) by (jf_rk_tac HS EE);
      let R22' := fresh "R22'" in jf_prreg HS (22%bv : bv 5) R22';
      eapply jf_post; first [eassumption | (rewrite R22'; exact E34) | jf_fds | jf_fs]
    end
  end
  end.

Lemma j_fits : j_fits_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
asink_none ameta_inv arodata_okS.
Proof.
unfold j_fits_stmt. intros LAWS AMEMCHR HSTK g pos mf nm tk dp W2 c2 Hstart Hwok.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HP as (HK & HDR & HDM & R27 & R11 & R12 & R13 & HNM).
pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP.
pose proof (SRr_run_pi_AJ B LAWS) as RUNP.
pose proof (SRr_run_pi_AJ_call B LAWS) as RUNC.
pose proof (paj_branch (PI := PI)) as BR.
pose proof HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
_ & _ & _ & _ & _ & HPRE & _).
pose proof HK as (Hbl & Rs7 & R24 & R21 & _).
pose proof HDR as (R6 & R18 & R25 & R26).
pose proof HDM as (Hznm & Hzdp & Hdp).
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro0 & _).
unfold V_nm, V_dp, N_nm, N_dp in R12, R18, R25, R26, Hznm, Hzdp, Hdp.
pose proof HNM as HNM'. unfold V_nm in HNM'.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
destruct (j_geo B LLVMF_STK LAWS g pos _ ly2 S2 W2 mem2 md2 HJ Hfrs)
as (EFa & HSF0 & HSF1 & HSF64 & Hsh0 & Hsh1 & Hsfsh).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (_ & _ & HSFapp).
rewrite EFa, HFB in HSFapp.
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
assert (Esh : shadow_addr (SFa g pos) = SHADOW_OFF + SFa g pos / 8) by reflexivity.
(* the model *)
pose proof (LLVMFuzzerTestOneInput_seg_J_model.m2_n_ld_le (e_pl g) Hwok) as Hnld.
pose proof (LLVMFuzzerTestOneInput_seg_J_model.m1_n_ln_le (e_pl g) Hwok) as Hnln.
pose proof (LLVMFuzzerTestOneInput_seg_J_model.m2_caps (e_pl g)) as Hcaps.
pose proof (LLVMFuzzerTestOneInput_seg_J_model.m2_r_cases (e_pl g)) as Hrc.
assert (EL3 : SlotModel.n_ld (e_pl g) = j_L3 (e_pl g) + 5).
{ unfold SlotModel.n_ld. rewrite LLVMFuzzerTestOneInput_seg_J_model.m2_len_dp. reflexivity. }
assert (HjL3 : 9 <= j_L3 (e_pl g)) by (clear - Hnln; unfold j_L3, j_L2, j_L1, j_d1, j_d2; lia).
assert (Hnulin : SFa g pos <= SFa g pos + 592 + SlotModel.n_ld (e_pl g) < SFa g pos + 1024)
by (clear - Hnld; lia).
(* the environment: atoms 32, 33, 34 are cap_name, cap_tok, cap_disp *)
remember (Eimg (Ereg regs2 (map (Z_to_bv 64) [SlotModel.t_cap_name (e_pl g); SlotModel.t_cap_tok (e_pl g);
SlotModel.t_cap_disp (e_pl g)]))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (SlotModel.t_cap_name (e_pl g)))
by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (SlotModel.t_cap_tok (e_pl g)))
by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (SlotModel.t_cap_disp (e_pl g)))
by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (ER : regs_ok E sr_atoms regs2) by (rewrite HE; apply regs_ok_Eimg_Ereg).
clear HE.
assert (U9 : bv_unsigned (ew E 9) = mf)
by (rewrite (EE 9%nat 9%bv eq_refl), Rs1; apply unsigned_lit_small; clear - Hmf0 H47 Hmfb Hshi C1; lia).
assert (U12 : bv_unsigned (ew E 12) = SFa g pos + 592 + j_L3 (e_pl g))
by (rewrite (EE 12%nat 12%bv eq_refl), R12; apply unsigned_lit_small; clear - HSF0 HSF1 C1 Hnld EL3 HjL3; lia).
assert (U12n : bv_unsigned (ew E 12) + 5 = SFa g pos + 592 + SlotModel.n_ld (e_pl g))
by (rewrite U12, EL3; ring).
assert (U13 : bv_unsigned (ew E 13) = j_L3 (e_pl g))
by (rewrite (EE 13%nat 13%bv eq_refl), R13; apply unsigned_lit_small; clear - Hnld EL3 HjL3; lia).
assert (U18 : bv_unsigned (ew E 18) = 2 ^ 64 - 1 - (SFa g pos + 592)).
{ rewrite (EE 18%nat 18%bv eq_refl), (jf_bvu _ _ R18). clear - HSF0 HSF1 C1. unfold Z.lnot. lia. }
assert (U23 : bv_unsigned (ew E 23) = shadow_addr (SFa g pos))
by (rewrite (EE 23%nat 23%bv eq_refl), Rs7; apply unsigned_lit_small; clear - Hsh0 Hsh1 C1; lia).
assert (U23s : bv_unsigned (ew E 23) + 86 = shadow_addr (SFa g pos) + 86) by (rewrite U23; reflexivity).
assert (U24 : bv_unsigned (ew E 24) = SlotModel.n_r (e_pl g) mod 2 ^ 64)
by (rewrite (EE 24%nat 24%bv eq_refl); exact (jf_bvu _ _ R24)).
assert (U27 : bv_unsigned (ew E 27) = SlotModel.n_ln (e_pl g))
by (rewrite (EE 27%nat 27%bv eq_refl), R27; apply unsigned_lit_small; clear - Hnln; lia).
assert (U32 : bv_unsigned (ew E 32) = SlotModel.t_cap_name (e_pl g))
by (rewrite E32; apply unsigned_lit_small; clear - Hcaps; lia).
assert (U33 : bv_unsigned (ew E 33) = SlotModel.t_cap_tok (e_pl g))
by (rewrite E33; apply unsigned_lit_small; clear - Hcaps; lia).
assert (U34 : bv_unsigned (ew E 34) = SlotModel.t_cap_disp (e_pl g))
by (rewrite E34; apply unsigned_lit_small; clear - Hcaps; lia).
(* the symbolic state at 0x82084 *)
assert (HS0 : st_ok_pi SEGS VAL E jf_ss0
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x1910)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold jf_ss0. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil.
    + unfold jf_r0, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [clear - Hmf0 C1; lia|]. split; [clear - Hmf0 H47 Hmfb Hshi; lia|].
      split; [intros o Ho; lia|].
      pose proof HK as (_ & _ & _ & _ & _ & _ & V144 & V128 & V120 & _).
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ mf 120 8 (SOff 34 0) (SlotModel.t_cap_disp (e_pl g)));
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | clear - Hcaps; lia | lia | exact V120].
      * apply (chunk_ok_val SEGS E _ mf 128 8 (SOff 33 0) (SlotModel.t_cap_tok (e_pl g)));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | clear - Hcaps; lia | lia | exact V128].
      * apply (chunk_ok_val SEGS E _ mf 144 8 (SOff 32 0) (SlotModel.t_cap_name (e_pl g)));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | clear - Hcaps; lia | lia | exact V144].
    + unfold jf_r1, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U12. split; [clear - HSF0 HjL3; lia|]. split; [clear - HSF1 C1 Hnld EL3 HjL3; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      apply (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
      [(4, pos)] ly2 S2 W2 mem2 md2 (4 * Z.of_nat (m_nrec g) + 7) (SFa g pos + 592 + j_L3 (e_pl g) + o) HJ ltac:(
      right; right; right; exists 4, pos; split; [left; reflexivity|]; left;
      unfold in_zr; cbn [fst snd]; rewrite EFa, HFB; clear - Ho Hnld EL3 HjL3; lia))).
    + unfold jf_r2, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U23. split; [clear - Hsh0; lia|]. split; [clear - Hsh1 C1; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      apply (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
      [(4, pos)] ly2 S2 W2 mem2 md2 (4 * Z.of_nat (m_nrec g) + 7) (shadow_addr (SFa g pos) + o) HJ ltac:(
      right; right; right; exists 4, pos; split; [left; reflexivity|]; right;
      unfold in_zr; cbn [fst snd]; rewrite EFa, HFB; clear - Ho; lia))).
  - apply pairwise_disjoint_of_extents. unfold jf_r0, jf_r1, jf_r2, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U12, U23.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hmf0 Hsh1 Hsfsh HSF0 HSF1 C1 Hnld EL3 HjL3. clear. intros. repeat split; lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [exact I | split; exact I]. }
pose proof (st_ok_pi_pin_reg' E jf_ss0 _ 11%bv 5 HS0 ltac:(cbn [ms_regs restrict mkst]; exact R11) eq_refl) as HS.
change (mkSS (ss_pc jf_ss0) (sr_set (ss_regs jf_ss0) 11%bv (SLit 5)) (ss_mem jf_ss0) (ss_resv jf_ss0)
  (ss_facts jf_ss0)) with jf_ss in HS.
clear HS0.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 4096 <= a < mf) ->
  a <> SFa g pos + 592 + SlotModel.n_ld (e_pl g) -> a <> shadow_addr (SFa g pos) + 86 ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W2) mem2 a) by (intros; reflexivity).
unfold cfg_at. change (w64 (BASE + 0x1910)) with (Z_to_bv 64 (BASE + 0x1910)).
(* ---- 0x82084 .. 0x8208c: x19 = x13 + 5, the trap above 63 ---- *)
paj_run_to_sh RUNTOP HS HJ 0x1988; [jf_awr_tac|].
jf_keep_tac W2 mem2 KEEP.
psrr_branch_pi RUNP BR HS.
{ exfalso. rewrite (jb_ltu_off E 13 5 63) in Hc by (clear; lia). rewrite U13, zcanon_id in Hc
  by (unfold M64; clear - Hnld EL3 HjL3; lia). apply Z.ltb_lt in Hc. clear - Hc Hnld EL3 HjL3. lia. }
clear Hc.
(* ---- 0x82090: the trap above the complement of &exp_dp ---- *)
paj_run_to_sh RUNTOP HS HJ 0x1988; [jf_awr_tac|].
jf_keep_tac W2 mem2 KEEP.
psrr_branch_pi RUNP BR HS.
{ exfalso. rewrite branch_ltu_U, (jf_U_offu E 18 0 _ U18), (jf_U_offu E 13 5 _ U13) in Hc
  by (clear - HSF0 HSF1 C1 Hnld EL3 HjL3; lia).
  apply Z.ltb_lt in Hc. clear - Hc HSF0 HSF1 C1 Hnld EL3 HjL3. lia. }
clear Hc.
(* ---- 0x82094 .. 0x820a0: the NUL of exp_dp, the name test ---- *)
paj_run_to_sh RUNTOP HS HJ 0x1988; [jf_awr_tac|].
jf_keep_tac W2 mem2 KEEP.
psrr_branch_pi RUNP BR HS.
{ (* the name does not fit: 0x820d8, x10 = 0, x22 = cap_disp, then 0x820ec *)
  rewrite branch_geu_U, (jf_U_offu E 27 0 _ U27), (jf_U_offu E 32 0 _ U32) in Hc by (clear - Hnln Hcaps; lia).
  apply Bool.negb_true_iff, Z.ltb_ge in Hc. rename Hc into HN.
  paj_run_to_sh RUNTOP HS HJ 0x1988; [jf_awr_tac|].
  jf_keep_tac W2 mem2 KEEP.
  psrr_branch_pi RUNP BR HS.
  - clear Hc. paj_run_to_sh RUNTOP HS HJ 0x1988; [jf_awr_tac|].
    jf_keep_tac W2 mem2 KEEP.
    jf_end HS EE E34.
  - exfalso. rewrite branch_eq_U, (jf_U_offu E 24 0 _ U24), U_SLit in Hc
    by (clear; pose proof (Z.mod_pos_bound (SlotModel.n_r (e_pl g)) (2 ^ 64) ltac:(lia)); lia).
    destruct Hrc as [Hr | Hr]; [|rewrite Hr in Hc; vm_compute in Hc; discriminate Hc].
    destruct (LLVMFuzzerTestOneInput_seg_J_model.m2_fits_r0 (e_pl g) Hr) as (_ & Hfn & _).
    rewrite !Z.add_0_r in HN. clear - HN Hfn. lia. }
rewrite branch_geu_U, (jf_U_offu E 27 0 _ U27), (jf_U_offu E 32 0 _ U32) in Hc by (clear - Hnln Hcaps; lia).
apply Bool.negb_false_iff, Z.ltb_lt in Hc. rename Hc into HN.
(* ---- 0x820a4 .. 0x820b0: memchr (&exp_nm, '-', n_ln) ---- *)
paj_run_shc RUNP RUNC HS HJ; [jf_awr_tac|].
jf_keep_tac W2 mem2 KEEP.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => rename m into msC end.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp1. prreg HS (3%bv : bv 5) Rgp1.
prreg HS (4%bv : bv 5) Rtp1.
rewrite (EE 25%nat 25%bv eq_refl), R25 in Ra0.
rewrite (EE 27%nat 27%bv eq_refl), R27 in Ra2.
rewrite (EE 2%nat 2%bv eq_refl), Rsp in Rsp1.
rewrite (EE 3%nat 3%bv eq_refl), Rgp in Rgp1.
rewrite (EE 4%nat 4%bv eq_refl), Rtp in Rtp1.
assert (Usp : spZ (ms_regs msC) = mf).
{ unfold spZ. rewrite Rsp1. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (HXT : forall i, 0 <= i < SlotModel.n_ln (e_pl g) ->
  aview SEGS (w_H W2) (ms_mem msC) (SFa g pos + 528 + i) =
  Some (RcIdentModel.bz (nth (Z.to_nat i) (SlotModel.n_EXP_NM (e_pl g)) (RcIdentModel.zb 0)))).
{ intros i Hi. rewrite KEEP by (clear - Hi Hmf0 HSF0 HSF1 Hsh1 Hsfsh C1 Hnld Hnln; lia).
  replace (SFa g pos + 528 + i) with (SFa g pos + 528 + Z.of_nat (Z.to_nat i)) by (clear - Hi; lia).
  rewrite (jf_aview_bytes W2 mem2 _ _ (Z.to_nat i) HNM').
  - rewrite app_nth1 by (unfold SlotModel.n_ln in Hi; clear - Hi; lia). reflexivity.
  - rewrite length_app. cbn [length]. unfold SlotModel.n_ln in Hi. clear - Hi. lia. }
assert (HSRC : src_ok SEGS W2 (ms_regs msC) (ms_mem msC) (SFa g pos + 528) (SlotModel.n_ln (e_pl g))).
{ intros a Ha. split.
  - replace a with (SFa g pos + 528 + (a - (SFa g pos + 528))) by (clear; lia).
    rewrite HXT by (clear - Ha; lia). discriminate.
  - rewrite Usp, Hes. clear - Ha Hmf0 HSF1 C1 Hnln. lia. }
assert (HAMR : amem_range (SFa g pos + 528) (SlotModel.n_ln (e_pl g))).
{ apply amem_range_high; [clear - Hnln; lia | | clear - HSF1 Hnln; lia].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HSFapp. clear - HSFapp Hnln. lia. }
assert (HRAc : range_addressable (aview SEGS (w_H W2) (ms_mem msC)) SHADOW_OFF (SFa g pos + 528)
  (SlotModel.n_ln (e_pl g))).
{ apply (range_addressable_sub _ SHADOW_OFF (SFa g pos + 528) 32); [| clear; lia | clear - Hnln; lia].
  apply zero_shadow_range; [clear - HSF64; lia | reflexivity |].
  apply (j_zero_shadow_moved (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W2) (ms_mem msC)) SHADOW_OFF
    (SFa g pos + 528) 32); [|exact Hznm].
  intros i Hi. apply KEEP; clear - Hi Hmf0 HSF0 HSF1 HSF64 Hsh1 Hsfsh C1 Esh Hnld;
  unfold shadow_of_addr; rewrite Esh in *; unfold SHADOW_OFF in *; lia. }
assert (HHULL : shadow_hull_vis (aview SEGS (w_H W2) (ms_mem msC)) (SFa g pos + 528) (SlotModel.n_ln (e_pl g))).
{ apply (shadow_hull_vis_of_frame SEGS B LAWS ly2 S2 W2 (ms_mem msC) _ 4 pos (SFa g pos + 528)
    (SlotModel.n_ln (e_pl g)) (proj1 HJ) Hin4);
  [rewrite EFa; clear; lia | rewrite EFa, HFB; clear - Hnln; lia | clear - Hnln; lia]. }
assert (HROc : aro_unowned SEGS B (aview SEGS (w_H W2) (ms_mem msC))).
{ apply (aro_unowned_of_arodata SEGS pa_relro_lo pa_relro_hi B).
  eapply (IdentBase.arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B);
  [exact HJ | exact (HRO _ Hro0)]. }
pmkst HS.
eapply SRr_bind.
{ exact (jf_memchr_at LAWS AMEMCHR W2 (ms_regs msC) (ms_mem msC) LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g)
    (e_mem g) (e_md g) [(4, pos)] ly2 S2 _ (4 * Z.of_nat (m_nrec g) + 7) (SFa g pos + 528) 45
    (SlotModel.n_ln (e_pl g)) (mf - e_sp0 g) (Z_to_bv 64 (BASE + 0x1940)) HJ Ra0 Ra1 Ra2
    ltac:(clear; lia) ltac:(clear - Hnln; lia) ltac:(clear - HSF0; lia) ltac:(clear - HSF1 C1 Hnln; lia)
    ltac:(rewrite Usp; clear; lia) ltac:(clear - Hmf32 Hsp0al; lia) ltac:(clear - Hmfb; lia)
    ltac:(clear - Hmfb HSTK' Hes Has; lia) Rgp1 Rtp1 Rra ltac:(apply ret_ok_codeptr_v; [clear; lia | reflexivity])
    HSRC HAMR HRAc (fun _ => HHULL) HROc). }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (kk & Hfb & Ha0kk) & Hfr3 & Hpres3 &
  Efd3 & Efs3).
rewrite Usp in Hfr3.
(* the state after the call, at 0x820b4: the three regions are kept (memchr writes only below sp = mf) *)
lazymatch type of HS with st_ok ?segs ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (pick (ss_mem ssx) [0; 1; 2]%nat) in
  let retk := eval vm_compute in (match sr_get (ss_regs ssx) 1 with SOff _ z => z | _ => 0 end) in
  pose proof (st_ok_pi_after_call 200%nat Ex ssx msx regs3 (mrestrict (w_H W2) mem3) rs retk HEI ltac:(clear; lia)
    HS eq_refl ltac:(clear; cbv; lia) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity)
    HP3) as HS3;
  let ss2 := eval vm_compute in (ss_after_call ssx rs 200%nat retk) in
  change (ss_after_call ssx rs 200%nat retk) with ss2 in HS3
end.
match type of HS3 with ?Q -> _ => assert (HQ : Q); [|specialize (HS3 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - eapply region_kept_aview; [exact U9 | | exact Hpres3].
    intros a Ha; apply Hfr3; rewrite ?Hes; clear - Ha Hmf0 Hmfb H47 Hshi C1; lia.
  - eapply region_kept_aview; [exact U12 | | exact Hpres3].
    intros a Ha; apply Hfr3; rewrite ?Hes; clear - Ha Hmf0 HSF0 HSF1 C1 Hnld EL3 HjL3; lia.
  - eapply region_kept_aview; [exact U23 | | exact Hpres3].
    intros a Ha; apply Hfr3; rewrite ?Hes; clear - Ha Hmf0 Hsh0 Hsh1 C1; lia. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
assert (HEI3 : img_env VAL A_LIM (havoc E 200 (map (getr regs3) CLOB)))
by (apply img_env_havoc; [exact HEI | apply Nat.leb_le; reflexivity]).
clear HJ. rename HJ3 into HJ.
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 4096 <= a < mf) ->
  a <> SFa g pos + 592 + SlotModel.n_ld (e_pl g) -> a <> shadow_addr (SFa g pos) + 86 ->
  aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha H1 H2 H3. rewrite (Hfr3 a Ha) by (rewrite Hes; exact H1). exact (KEEP a Ha H1 H2 H3). }
clear KEEP. rename K3 into KEEP.
assert (FDS3 : m_fds md3 = m_fds md2) by (rewrite Efd3; jf_fds).
assert (FS3 : m_fs md3 = m_fs md2) by (rewrite Efs3; jf_fs).
(* memchr's answer is the model's first dash *)
destruct (LLVMFuzzerTestOneInput_seg_J_model.m1_dash_find (e_pl g)) as (k0 & Hk0 & Hpre0 & Hat0 & Hd0).
assert (Ekk : kk = k0).
{ apply (jf_first_byte_eq W2 (ms_mem msC) (SFa g pos + 528) (SlotModel.n_ln (e_pl g)) 45 kk k0 Hfb Hk0).
  - intros j Hj. exists (RcIdentModel.bz (nth (Z.to_nat j) (SlotModel.n_EXP_NM (e_pl g)) (RcIdentModel.zb 0))).
    split; [apply HXT; clear - Hj Hk0; lia | apply Hpre0; exact Hj].
  - intros Hlt. rewrite HXT by (clear - Hlt Hk0; lia). rewrite (Hat0 Hlt). reflexivity. }
subst kk.
(* the atoms after the call *)
assert (U9' : bv_unsigned (ew (havoc E 200 (map (getr regs3) CLOB)) 9) = mf)
by (rewrite ew_havoc_old by (clear; lia); exact U9).
assert (U12n' : bv_unsigned (ew (havoc E 200 (map (getr regs3) CLOB)) 12) + 5 =
  SFa g pos + 592 + SlotModel.n_ld (e_pl g)) by (rewrite ew_havoc_old by (clear; lia); exact U12n).
assert (U13' : bv_unsigned (ew (havoc E 200 (map (getr regs3) CLOB)) 13) = j_L3 (e_pl g))
by (rewrite ew_havoc_old by (clear; lia); exact U13).
assert (U23' : bv_unsigned (ew (havoc E 200 (map (getr regs3) CLOB)) 23) = shadow_addr (SFa g pos))
by (rewrite ew_havoc_old by (clear; lia); exact U23).
assert (U23s' : bv_unsigned (ew (havoc E 200 (map (getr regs3) CLOB)) 23) + 86 = shadow_addr (SFa g pos) + 86)
by (rewrite ew_havoc_old by (clear; lia); exact U23s).
assert (U24' : bv_unsigned (ew (havoc E 200 (map (getr regs3) CLOB)) 24) = SlotModel.n_r (e_pl g) mod 2 ^ 64)
by (rewrite ew_havoc_old by (clear; lia); exact U24).
assert (U27' : bv_unsigned (ew (havoc E 200 (map (getr regs3) CLOB)) 27) = SlotModel.n_ln (e_pl g))
by (rewrite ew_havoc_old by (clear; lia); exact U27).
assert (U33' : bv_unsigned (ew (havoc E 200 (map (getr regs3) CLOB)) 33) = SlotModel.t_cap_tok (e_pl g))
by (rewrite ew_havoc_old by (clear; lia); exact U33).
assert (U34' : bv_unsigned (ew (havoc E 200 (map (getr regs3) CLOB)) 34) = SlotModel.t_cap_disp (e_pl g))
by (rewrite ew_havoc_old by (clear; lia); exact U34).
assert (E204 : ew (havoc E 200 (map (getr regs3) CLOB)) 204 = getr regs3 10)
by (cbn [ew havoc Nat.ltb Nat.leb Nat.sub nth map CLOB]; reflexivity).
assert (U204 : bv_unsigned (ew (havoc E 200 (map (getr regs3) CLOB)) 204) =
  if k0 <? SlotModel.n_ln (e_pl g) then SFa g pos + 528 + k0 else 0).
{ rewrite E204, Ha0kk. destruct (k0 <? SlotModel.n_ln (e_pl g)) eqn:Hkl.
  - apply unsigned_lit_small. apply Z.ltb_lt in Hkl. clear - Hkl Hk0 HSF0 HSF1 C1 Hnln. lia.
  - apply unsigned_lit_small. clear. lia. }
assert (UTL : U (havoc E 200 (map (getr regs3) CLOB))
  (SAlu ALU_SUB (SOff 27 0) (SAlu ALU_SLTU (SLit 0) (SOff 204 0))) = SlotModel.n_lt (e_pl g)).
{ rewrite LLVMFuzzerTestOneInput_seg_J_model.m1_n_lt, <- Hd0.
  rewrite !U_SAlu, U_SLit, !U_SOff, U27', U204, !Z.add_0_r.
  destruct (k0 <? SlotModel.n_ln (e_pl g)) eqn:Hkl; cbv iota.
  - apply Z.ltb_lt in Hkl. rewrite jf_utl by (clear - Hkl Hk0 Hnln HSF0 HSF1 C1; lia).
    replace (0 <? SFa g pos + 528 + k0) with true by (symmetry; apply Z.ltb_lt; clear - HSF0 Hk0; lia).
    reflexivity.
  - rewrite jf_utl by (clear - Hnln; lia). reflexivity. }
(* ---- 0x820b4 .. 0x820c4: x10 = the token's length, x22 = cap_disp, the token test ---- *)
paj_run_to_sh RUNTOP HS HJ 0x1988; [jf_awr_tac|].
jf_keep_tac W2 mem2 KEEP.
psrr_branch_pi RUNP BR HS.
{ (* the token does not fit: 0x820e4, x10 = 0, then 0x820ec *)
  rewrite branch_geu_U, UTL, (jf_U_offu _ 33 0 _ U33') in Hc by (clear - Hcaps; lia).
  apply Bool.negb_true_iff, Z.ltb_ge in Hc. rename Hc into HT.
  paj_run_to_sh RUNTOP HS HJ 0x1988; [jf_awr_tac|].
  jf_keep_tac W2 mem2 KEEP.
  psrr_branch_pi RUNP BR HS.
  - clear Hc. paj_run_to_sh RUNTOP HS HJ 0x1988; [jf_awr_tac|].
    jf_keep_tac W2 mem2 KEEP.
    jf_end HS EE E34.
  - exfalso. rewrite branch_eq_U, (jf_U_offu _ 24 0 _ U24'), U_SLit in Hc
    by (clear; pose proof (Z.mod_pos_bound (SlotModel.n_r (e_pl g)) (2 ^ 64) ltac:(lia)); lia).
    destruct Hrc as [Hr | Hr]; [|rewrite Hr in Hc; vm_compute in Hc; discriminate Hc].
    destruct (LLVMFuzzerTestOneInput_seg_J_model.m2_fits_r0 (e_pl g) Hr) as (_ & _ & Hft & _).
    clear - HT Hft. lia. }
rewrite branch_geu_U, UTL, (jf_U_offu _ 33 0 _ U33') in Hc by (clear - Hcaps; lia).
apply Bool.negb_false_iff, Z.ltb_lt in Hc. rename Hc into HT.
(* ---- 0x820c8 .. 0x820cc: x10 = (x19 < cap_disp), the test of reac_box_name's answer ---- *)
paj_run_to_sh RUNTOP HS HJ 0x1988; [jf_awr_tac|].
jf_keep_tac W2 mem2 KEEP.
psrr_branch_pi RUNP BR HS.
{ (* n_r = 0: 0x820e8 *)
  rewrite branch_eq_U, (jf_U_offu _ 24 0 _ U24'), U_SLit in Hc
  by (clear; pose proof (Z.mod_pos_bound (SlotModel.n_r (e_pl g)) (2 ^ 64) ltac:(lia)); lia).
  assert (Hr : SlotModel.n_r (e_pl g) = 0)
  by (destruct Hrc as [Hr | Hr]; [exact Hr | rewrite Hr in Hc; vm_compute in Hc; discriminate Hc]).
  clear Hc.
  paj_run_to_sh RUNTOP HS HJ 0x1988; [jf_awr_tac|].
  jf_keep_tac W2 mem2 KEEP.
  psrr_branch_pi RUNP BR HS.
  - exfalso. rewrite branch_eq_U, (jf_U_offu _ 24 0 _ U24'), U_SLit in Hc
    by (clear; pose proof (Z.mod_pos_bound (SlotModel.n_r (e_pl g)) (2 ^ 64) ltac:(lia)); lia).
    rewrite Hr in Hc. vm_compute in Hc. discriminate Hc.
  - clear Hc. paj_run_to_sh RUNTOP HS HJ 0x1988; [jf_awr_tac|].
    jf_keep_tac W2 mem2 KEEP.
    psrr_branch_pi RUNP BR HS.
    + (* x10 = 0 would abort at 0x82614; with n_r = 0 the display fits, so x10 = 1 *)
      exfalso. rewrite branch_eq_U, U_SAlu, (jf_U_offu _ 13 5 _ U13'), (jf_U_offu _ 34 0 _ U34'), U_SLit in Hc
      by (clear - Hnld EL3 HjL3 Hcaps; lia).
      cbn [zalu_raw] in Hc.
      destruct (LLVMFuzzerTestOneInput_seg_J_model.m2_fits_r0 (e_pl g) Hr) as (_ & _ & _ & Hfd).
      replace (j_L3 (e_pl g) + 5 <? SlotModel.t_cap_disp (e_pl g) + 0) with true in Hc
      by (symmetry; apply Z.ltb_lt; clear - Hfd EL3; lia).
      vm_compute in Hc. discriminate Hc.
    + clear Hc. paj_run_to_sh RUNTOP HS HJ 0x1988; [jf_awr_tac|].
      jf_keep_tac W2 mem2 KEEP.
      jf_end HS EE E34. }
(* n_r <> 0, so n_r = -1: 0x820d0 *)
rewrite branch_eq_U, (jf_U_offu _ 24 0 _ U24'), U_SLit in Hc
by (clear; pose proof (Z.mod_pos_bound (SlotModel.n_r (e_pl g)) (2 ^ 64) ltac:(lia)); lia).
assert (Hr : SlotModel.n_r (e_pl g) = -1)
by (destruct Hrc as [Hr | Hr]; [rewrite Hr in Hc; vm_compute in Hc; discriminate Hc | exact Hr]).
clear Hc.
paj_run_to_sh RUNTOP HS HJ 0x1988; [jf_awr_tac|].
jf_keep_tac W2 mem2 KEEP.
psrr_branch_pi RUNP BR HS.
{ (* the display does not fit: 0x820e8 *)
  clear Hc. paj_run_to_sh RUNTOP HS HJ 0x1988; [jf_awr_tac|].
  jf_keep_tac W2 mem2 KEEP.
  psrr_branch_pi RUNP BR HS.
  - clear Hc. paj_run_to_sh RUNTOP HS HJ 0x1988; [jf_awr_tac|].
    jf_keep_tac W2 mem2 KEEP.
    jf_end HS EE E34.
  - exfalso. rewrite branch_eq_U, (jf_U_offu _ 24 0 _ U24'), U_SLit in Hc
    by (clear; pose proof (Z.mod_pos_bound (SlotModel.n_r (e_pl g)) (2 ^ 64) ltac:(lia)); lia).
    rewrite Hr in Hc. vm_compute in Hc. discriminate Hc. }
(* all three fit with n_r = -1: the abort at 0x820d4, which the model rules out *)
exfalso. rewrite branch_geu_U, (jf_U_offu _ 13 5 _ U13'), (jf_U_offu _ 34 0 _ U34') in Hc
by (clear - Hnld EL3 HjL3 Hcaps; lia).
apply Bool.negb_false_iff, Z.ltb_lt in Hc.
destruct (LLVMFuzzerTestOneInput_seg_J_model.m2_fits_rm1 (e_pl g) Hwok Hr) as [Hb | [Hb | Hb]];
clear - Hb HN HT Hc EL3; lia.
Qed.

End c.
End b.
End a.
