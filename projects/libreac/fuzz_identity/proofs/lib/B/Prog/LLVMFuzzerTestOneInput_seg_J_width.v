(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:1527-1530
   [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan build (lib/B). The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACes.v:251-253 [Apache-2.0]. The [Apache-2.0 OR MIT] text is used under
   Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_fits.v, with its addresses changed; 431 of its 539 lines of code are new or changed and 689 lines of the source are left out. *)
(* Segment J of LLVMFuzzerTestOneInput's build-B walk (fuzz_identity.asan-ubsan), the piece +0x13ec .. +0x1440
   (0x81b60 .. 0x81bb4), with the bad-width exit at +0x1988 (0x820fc): j_width_stmt of
   lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_pre.v.

   What the code does (a plain run, no checked access, no call):
     0x81b60 x11 := -1
     0x81b64 branch to 0x81b6c when x24 = x11      x24 is reac_box_name's answer, SlotModel.n_r
     0x81b68 jump to 0x82614 (abort) when x10 = 0  refuted: n_r is 0 or -1 (m2_r_cases), and n_r = 0 makes
                                                   n_wok true (m2_fits_r0), so x10 = 1 whenever x24 = 0
     0x81b6c x11 := the word at mf+64              the frame address
     0x81b70 x25 := x11 + 528                      &exp_nm
     0x81b74 x26 := x11 + 592                      &exp_dp
     0x81b78..0x81ba4 twelve byte stores of 0 at x23 + 66, 67, 68, 69, 78, 79, 80, 81, 74, 75, 76, 77
                                                   the shadow of exp_nm (4 granules) and of exp_dp (8)
     0x81ba8 the byte at x26 := 0                  exp_dp[0]
     0x81bac the byte at x25 := 0                  exp_nm[0]
     0x81bb0 jump to 0x820fc when x10 = 0          bad widths: straight to inv_J_end's own slot
   and otherwise falls to 0x81bb4, which is jc1's slot.

   The run starts from the three-region state ss_j1 0x13ec of lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_pre.v
   (the machine-frame words read-only, the frame bytes [SF+528, SF+593) and the frame's shadow cells
   [sh+66, sh+82) writable), with x10 and x24 pinned to the literals of the case, so that the engine decides
   both branches itself. The run writes only the two windows, so every other byte is kept (jw_keep). *)
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
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* The frame's shadow cells need lia's division handling, which YC4b turns off. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* The start state of the run: ss_j1 0x13ec with x10 (the width answer) and x24 (reac_box_name's answer)
   pinned to the literals of the case. *)
Definition ss_jw (z10 z24 : Z) : sstate :=
mkSS 0x13ec (sr_set (sr_set sr_atoms 10%bv (SLit z10)) 24%bv (SLit z24)) [j1_mf; j1_sf; j1_sh] None
(mkFacts [] [] []).

(* Membership in a literal list, by walking it. (`tauto` would pick up unused Section variables.) *)
Local Ltac jw_in := cbn [In]; repeat (first [left; reflexivity | right]).

(* ---- the model: the token's length, as the three buffers' bound needs it ------------------------------- *)
Lemma jw_tok_true : forall l, length (SlotModel.tok_go true l) = length l.
Proof.
induction l as [|b r IH]; [reflexivity|]. cbn [SlotModel.tok_go negb andb length]. rewrite IH. reflexivity.
Qed.
Lemma jw_tok_false : forall l, Z.of_nat (length (SlotModel.tok_go false l)) =
Z.of_nat (length l) - (if SlotModel.has_dash l then 1 else 0).
Proof.
unfold SlotModel.has_dash. induction l as [|b r IH]; [reflexivity|].
cbn [SlotModel.tok_go existsb negb andb].
destruct (RcIdentModel.bz b =? 45); cbn [orb length].
- rewrite jw_tok_true. lia.
- rewrite Nat2Z.inj_succ, IH. destruct (existsb _ r); lia.
Qed.
Lemma jw_tk_len : forall inp, Z.of_nat (length (SlotModel.n_TK inp)) = SlotModel.n_lt inp.
Proof. intro inp. unfold SlotModel.n_TK, SlotModel.TOK. rewrite jw_tok_false. reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).

(* ---- what the run keeps: every byte outside the two write windows -------------------------------------- *)
Definition jw_keep (W : world SEGS) (SF sh : Z) (m m' : word -> option byte) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (SF + 528 <= a < SF + 593) -> ~ (sh + 66 <= a < sh + 82) ->
aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.

(* The run's write windows are the frame bytes [SF+528, SF+593) and the frame's shadow cells [sh+66, sh+82),
   both of them bytes of the entry's own class-4 frame. *)
Lemma jw_awr : forall E (z10 z24 : Z) STK sp0 FP bl0 blc ly pos SF,
frame_addr ly 4 pos = SF -> bv_unsigned (ew E 32%nat) = SF ->
bv_unsigned (ew E 23%nat) = shadow_addr SF ->
awr_ok E (ss_mem (ss_jw z10 z24)) STK sp0 FP bl0 blc ly [(4, pos)].
Proof.
intros E z10 z24 STK sp0 FP bl0 blc ly pos SF EFa U32 U23.
cbn [ss_jw ss_mem].
apply awr_ok_cons_ro; [cbn [j1_mf YP09.r_wlo YP09.r_whi]; clear; lia|].
apply (awr_ok_cons_gen E j1_sf _ STK sp0 FP bl0 blc ly [(4, pos)] 32%nat SF); [reflexivity | exact U32 | |].
{ intros a Ha. cbn [j1_sf YP09.r_wlo YP09.r_whi] in Ha.
  right; right; right. exists 4, pos. split; [left; reflexivity|]. left.
  unfold in_zr. cbn [fst snd]. rewrite EFa. change (fs_frame_bytes 4) with 1024. clear - Ha. lia. }
apply (awr_ok_cons_gen E j1_sh _ STK sp0 FP bl0 blc ly [(4, pos)] 23%nat (shadow_addr SF));
[reflexivity | exact U23 | |].
{ intros a Ha. cbn [j1_sh YP09.r_wlo YP09.r_whi] in Ha.
  right; right; right. exists 4, pos. split; [left; reflexivity|]. right.
  unfold in_zr. cbn [fst snd]. rewrite EFa. change (fs_frame_bytes 4 / 8) with 128. clear - Ha. lia. }
apply awr_ok_nil.
Qed.

(* A byte the run stored, read off a region of the state it ended in. *)
Lemma jw_byte0 : forall E (m : word -> option byte) n b lo hi wlo whi cs od,
YP09.region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 1 (SLit 0))) cs ->
val_mem SEGS m (b + od) 1 0.
Proof.
intros E m n b lo hi wlo whi cs od HR Hb Hin.
exact (field_of_region E m n b cs lo hi wlo whi od 1%N (SLit 0) 0 HR Hb Hin eq_refl
ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)).
Qed.
Lemma jw_sh0 : forall E (W : world SEGS) (m : word -> option byte) n b lo hi wlo whi cs od a,
YP09.region_ok SEGS E (mrestrict (w_H W) m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 1 (SLit 0))) cs -> a = b + od ->
aview SEGS (w_H W) m a = Some 0.
Proof.
intros E W m n b lo hi wlo whi cs od a HR Hb Hin ->.
apply aview_of_val_mem1; [exact (jw_byte0 E _ n b lo hi wlo whi cs od HR Hb Hin) | lia].
Qed.

(* The two frame bytes and the two cleared shadow windows, from the regions of the state the run ended in. *)
Lemma jw_mem_facts : forall E (W : world SEGS) (m : word -> option byte) SF cs1 cs2,
bv_unsigned (ew E 32%nat) = SF -> bv_unsigned (ew E 23%nat) = shadow_addr SF ->
YP09.region_ok SEGS E (mrestrict (w_H W) m) (YP09.mkRegion (Some 32%nat) 528 593 528 593 cs1) ->
YP09.region_ok SEGS E (mrestrict (w_H W) m) (YP09.mkRegion (Some 23%nat) 66 82 66 82 cs2) ->
In (YP09.mkChunk 528 (CVal 1 (SLit 0))) cs1 -> In (YP09.mkChunk 592 (CVal 1 (SLit 0))) cs1 ->
(forall od, In od [66; 67; 68; 69; 74; 75; 76; 77; 78; 79; 80; 81] ->
In (YP09.mkChunk od (CVal 1 (SLit 0))) cs2) ->
val_mem SEGS (mrestrict (w_H W) m) (SF + V_nm) 1 0 /\
val_mem SEGS (mrestrict (w_H W) m) (SF + V_dp) 1 0 /\
sh_zero W m (SF + V_nm) N_nm /\ sh_zero W m (SF + V_dp) N_dp.
Proof.
intros E W m SF cs1 cs2 U32 U23 HR1 HR2 I528 I592 Ish.
assert (Ecell : forall off c0 i, off = 8 * c0 ->
shadow_of_addr SHADOW_OFF (SF + off) + i = shadow_addr SF + (c0 + i)).
{ intros off c0 i ->. unfold shadow_of_addr, shadow_addr.
  replace (SF + 8 * c0) with (SF + c0 * 8) by (clear; lia).
  rewrite Z.div_add by (clear; lia). clear; lia. }
split; [exact (jw_byte0 E _ 32%nat SF 528 593 528 593 cs1 528 HR1 U32 I528)|].
split; [exact (jw_byte0 E _ 32%nat SF 528 593 528 593 cs1 592 HR1 U32 I592)|].
split.
- intros i Hi. change (N_nm / 8) with 4 in Hi.
  rewrite (Ecell V_nm 66 i eq_refl).
  apply (jw_sh0 E W m 23%nat (shadow_addr SF) 66 82 66 82 cs2 (66 + i) _ HR2 U23); [|reflexivity].
  apply Ish. assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by (clear - Hi; lia).
  destruct Hc as [-> | [-> | [-> | ->]]]; jw_in.
- intros i Hi. change (N_dp / 8) with 8 in Hi.
  rewrite (Ecell V_dp 74 i eq_refl).
  apply (jw_sh0 E W m 23%nat (shadow_addr SF) 66 82 66 82 cs2 (74 + i) _ HR2 U23); [|reflexivity].
  apply Ish.
  assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by (clear - Hi; lia).
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; jw_in.
Qed.

Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
(* The contract's own stack bound (lib/B/Prog/LLVMFuzzerTestOneInput.v), as the prefix file states it for
   j1_entry: the piece's symbolic start state is j1_entry's and needs it. *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
#[local] Notation ACUT := (acut B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation JKEEP := (jkeep B).
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation JC0 := (jc0 B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation JC1 := (jc1 B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation INVJ := (inv_J_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).

(* ---- the two exit cuts, from the facts the run leaves ---------------------------------------------------- *)
Lemma jw_post : AR_laws SEGS B ->
forall (g : ectx) pos mf nm tk dp ly2 S2 (W2 : world SEGS) regs2 mem2 md2 regs3 mem3 md3,
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly2 S2 W2 mem3 md3 (4 * Z.of_nat (m_nrec g) + 7) ->
frames S2 = [(4, pos)] ->
0 <= 4 * Z.of_nat (m_nrec g) + 7 <= EV_LLVMF ->
mo_le MT (e_S g) S2 ((4 * Z.of_nat (m_nrec g) + 7) * MEV MT) ->
mo_ok MT S2 ((EV_LLVMF - (4 * Z.of_nat (m_nrec g) + 7)) * MEV MT) ->
ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
JKEEP g pos mf nm tk dp ly2 S2 W2 regs2 mem2 ->
mf_id3 g pos mf W2 mem2 ->
getr regs2 12 = w64 SHADOW_OFF ->
getr regs2 18 = w64 (SlotModel.n_fam (e_pl g)) ->
getr regs2 27 = w64 (RcIdentModel.has_model_name (m_id g (m_nrec g))) ->
getr regs2 22 = w64 (SlotModel.t_cap_disp (e_pl g)) ->
jw_keep W2 (SFa g pos) (shadow_addr (SFa g pos)) mem2 mem3 ->
val_mem SEGS (rd W2 mem3) (SFa g pos + V_nm) 1 0 ->
val_mem SEGS (rd W2 mem3) (SFa g pos + V_dp) 1 0 ->
sh_zero W2 mem3 (SFa g pos + V_nm) N_nm ->
sh_zero W2 mem3 (SFa g pos + V_dp) N_dp ->
(forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 12%bv; 18%bv; 21%bv; 22%bv; 23%bv; 27%bv] ->
getr regs3 r = getr regs2 r) ->
getr regs3 24 = w64 (SlotModel.n_r (e_pl g)) ->
getr regs3 25 = w64 (SFa g pos + V_nm) ->
getr regs3 26 = w64 (SFa g pos + V_dp) ->
m_fds md3 = m_fds md2 -> m_fs md3 = m_fs md2 ->
JC1 g pos mf nm tk dp W2 (cfg_at SEGS (BASE + 0x1440) regs3 mem3 md3) /\
(SlotModel.n_wok (e_pl g) = false ->
INVJ g pos mf nm tk dp W2 (cfg_at SEGS (BASE + 0x1988) regs3 mem3 md3)).
Proof.
intros LAWS g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3
HJ Hfrs Hk MLE MOK HC HK Hmf3 R12 R18 R27 R22 K VNM VDP ZNM ZDP RK R24 R25 R26 Efds Efs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & H0STK & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
assert (Has : ASTACK = 16384) by reflexivity.
destruct (j_geo B LLVMF_STK LAWS g pos _ ly2 S2 W2 mem3 md3 HJ Hfrs)
as (EFa & HSF0 & HSF1 & HSF64 & Hsh0 & Hsh1 & Hsfsh).
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
V24 & V32 & V40 & V48 & V56 & V64b & V72 & V80 & V88 & V96 & V104 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct HK as (Hbl & Rs7 & R24b & R21 & V152 & V184 & V144 & V128 & V120 & V176 & V160 & V112 & Hid & Hbufs).
assert (HmfA : alloc_ceiling + 16368 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
assert (Hsp47 : e_sp0 g <= 2 ^ 47) by (clear - Hshi H47; lia).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
(* the transports over the run's two windows *)
assert (VMS : forall a (n : nat) v, mf <= a -> a + Z.of_nat n <= e_sp0 g ->
val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 mem3) a n v).
{ intros a n v H1 H2 Hv. apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 mem3 a a n v); [|exact Hv].
  intros kk Hkk. apply K; clear - H1 H2 Hkk HmfA Hsp47 Hmfb HSF1 Hsh1 C1; lia. }
assert (VMF : forall off (n : nat) v, 0 <= off -> off + Z.of_nat n <= 1024 ->
(off + Z.of_nat n <= 528 \/ 593 <= off) ->
val_mem SEGS (rd W2 mem2) (SFa g pos + off) n v -> val_mem SEGS (rd W2 mem3) (SFa g pos + off) n v).
{ intros off n v H0 H1 H2 Hv.
  apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 mem3 (SFa g pos + off) (SFa g pos + off) n v); [|exact Hv].
  intros kk Hkk. apply K; clear - H0 H1 H2 Hkk HSF0 HSF1 Hsh1 Hsfsh C1; lia. }
assert (SHID : forall (i : Z), 0 <= i < 5 ->
aview SEGS (w_H W2) mem3 (shadow_of_addr SHADOW_OFF (SFa g pos + V_id) + i) =
aview SEGS (w_H W2) mem2 (shadow_of_addr SHADOW_OFF (SFa g pos + V_id) + i)).
{ intros i Hi.
  assert (Ea : shadow_of_addr SHADOW_OFF (SFa g pos + V_id) + i = shadow_addr (SFa g pos) + (44 + i)).
  { unfold shadow_of_addr, shadow_addr, V_id.
    replace (SFa g pos + 352) with (SFa g pos + 44 * 8) by (clear; lia).
    rewrite Z.div_add by (clear; lia). clear; lia. }
  rewrite Ea. apply K; clear - Hi HSF0 HSF1 Hsh0 Hsh1 Hsfsh C1; lia. }
assert (GAH : forall b m a l, In (b, m) (ablocks B ly2 S2) -> 0 <= m -> b <= a ->
a + Z.of_nat (length l) <= b + req_size m ->
garr8 SEGS (rd W2 mem2) a l -> garr8 SEGS (rd W2 mem3) a l).
{ intros b m a l Hin Hm H1 H2 Hg.
  destruct (al_blocks SEGS B LAWS ly2 S2 W2 mem3 md3 b m HAR Hin) as (_ & H4096 & Hceilb & Happ & _).
  pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem3 md3 b m 4 pos HAR Hin Hin4) as Hsep.
  rewrite EFa in Hsep. change (fs_frame_bytes 4) with 1024 in Hsep.
  unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
  apply (j_garr8_moved SEGS (w_H W2) (w_H W2) mem2 mem3 a l); [|exact Hg].
  intros kk Hkk. apply K.
  - clear - H1 H2 Hkk H4096 Hceilb C1. lia.
  - clear - H1 H2 Hkk Hsep HSF0 HSF1. lia.
  - intros Hsh. apply (fshadow_not_app (SFa g pos) 128 b (req_size m) (a + kk));
    [ clear - HSF0; lia | clear - HSF1 C1; lia | exact Happ
    | clear - Hsh; unfold shadow_addr, SHADOW_OFF in Hsh; lia
    | clear - H1 H2 Hkk; lia ]. }
(* the machine-frame words the two cuts read *)
assert (W152 : val_mem SEGS (rd W2 mem3) (mf + 152) 8 nm)
by (apply VMS; [clear; lia | clear - Hmfb; lia | exact V152]).
assert (W184 : val_mem SEGS (rd W2 mem3) (mf + 184) 8 dp)
by (apply VMS; [clear; lia | clear - Hmfb; lia | exact V184]).
assert (W144 : val_mem SEGS (rd W2 mem3) (mf + 144) 8 (SlotModel.t_cap_name (e_pl g)))
by (apply VMS; [clear; lia | clear - Hmfb; lia | exact V144]).
assert (W128 : val_mem SEGS (rd W2 mem3) (mf + 128) 8 (SlotModel.t_cap_tok (e_pl g)))
by (apply VMS; [clear; lia | clear - Hmfb; lia | exact V128]).
assert (W120 : val_mem SEGS (rd W2 mem3) (mf + 120) 8 (SlotModel.t_cap_disp (e_pl g)))
by (apply VMS; [clear; lia | clear - Hmfb; lia | exact V120]).
assert (W176 : val_mem SEGS (rd W2 mem3) (mf + 176) 8 (SlotModel.t_in (e_pl g)))
by (apply VMS; [clear; lia | clear - Hmfb; lia | exact V176]).
assert (W160 : val_mem SEGS (rd W2 mem3) (mf + 160) 8 (SlotModel.t_out (e_pl g)))
by (apply VMS; [clear; lia | clear - Hmfb; lia | exact V160]).
assert (W112 : val_mem SEGS (rd W2 mem3) (mf + 112) 8 (SlotModel.t_row (e_pl g)))
by (apply VMS; [clear; lia | clear - Hmfb; lia | exact V112]).
assert (HID3 : mf_id3 g pos mf W2 mem3).
{ unfold mf_id3 in Hmf3 |- *. apply VMS; [clear; lia | clear - Hmfb; lia | exact Hmf3]. }
(* the record's `id`, kept with its shadow *)
assert (IDK : id_at g pos (m_nrec g) W2 mem3).
{ destruct Hid as (Hidb & Hidz & Hidk). unfold id_at. split; [|split].
  - unfold bytes_at8 in Hidb |- *. apply (j_garr8_moved SEGS (w_H W2) (w_H W2) mem2 mem3 _ _); [|exact Hidb].
    intros j Hj. rewrite length_map in Hj. unfold m_id in Hj. rewrite SlotModel.rec_id_length in Hj.
    unfold RcIdentModel.ID_SIZE in Hj. apply K;
    clear - Hj HSF0 HSF1 Hsh1 Hsfsh C1; unfold V_id; lia.
  - unfold sh_zero in Hidz |- *.
    apply (j_zero_shadow_moved (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W2) mem3) SHADOW_OFF
    (SFa g pos + V_id) N_id); [|exact Hidz].
    intros i Hi. apply SHID. clear - Hi. unfold N_id in Hi. lia.
  - unfold sh_blk in Hidk |- *.
    apply (j_block_shadow_moved (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W2) mem3) SHADOW_OFF
    (SFa g pos + V_id) N_id); [|exact Hidk].
    intros i Hi. apply SHID. clear - Hi. unfold N_id in Hi. lia. }
(* the three heap buffers, when reac_box_name wrote them *)
assert (HBUF : SlotModel.n_r (e_pl g) = 0 ->
bytes_at8 W2 mem3 nm (SlotModel.n_EXP_NM (e_pl g) ++ [RcIdentModel.zb 0]) /\
bytes_at8 W2 mem3 tk (SlotModel.n_TK (e_pl g) ++ [RcIdentModel.zb 0]) /\
bytes_at8 W2 mem3 dp (SlotModel.n_EXP_DP (e_pl g) ++ [RcIdentModel.zb 0])).
{ intros Hr0. destruct (Hbufs Hr0) as (Bnm & Btk & Bdp).
  destruct (LLVMFuzzerTestOneInput_seg_J_model.m2_fits_r0 (e_pl g) Hr0) as (_ & Hfn & Hft & Hfd).
  assert (INB : forall h, In h [(nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1);
  (tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1); (dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1)] ->
  In h (ablocks B ly2 S2)).
  { intros h Hh. destruct Hbl as [Hperm _].
    apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left. exact Hh. }
  pose proof (req_size_pos (Z.max (SlotModel.t_cap_name (e_pl g)) 1) ltac:(clear; lia)) as Q1.
  pose proof (req_size_pos (Z.max (SlotModel.t_cap_tok (e_pl g)) 1) ltac:(clear; lia)) as Q2.
  pose proof (req_size_pos (Z.max (SlotModel.t_cap_disp (e_pl g)) 1) ltac:(clear; lia)) as Q3.
  pose proof (jw_tk_len (e_pl g)) as Ltk.
  unfold bytes_at8 in *. split; [|split].
  - apply (GAH nm (Z.max (SlotModel.t_cap_name (e_pl g)) 1) nm);
    [apply INB; jw_in | clear; lia | clear; lia | | exact Bnm].
    rewrite length_map, length_app. cbn [length]. unfold SlotModel.n_ln in Hfn. clear - Hfn Q1. lia.
  - apply (GAH tk (Z.max (SlotModel.t_cap_tok (e_pl g)) 1) tk);
    [apply INB; jw_in | clear; lia | clear; lia | | exact Btk].
    rewrite length_map, length_app. cbn [length]. clear - Hft Q2 Ltk. lia.
  - apply (GAH dp (Z.max (SlotModel.t_cap_disp (e_pl g)) 1) dp);
    [apply INB; jw_in | clear; lia | clear; lia | | exact Bdp].
    rewrite length_map, length_app. cbn [length]. unfold SlotModel.n_ld in Hfd. clear - Hfd Q3. lia. }
(* the input block *)
assert (HINB : bytes_at8 W2 mem3 (e_p g) (e_pl g)).
{ pose proof HPRE as (_ & _ & _ & _ & Hinp & Hlen & _).
  destruct Hinp as [[Hne Hpe] | [Hn Hine]].
  - unfold bytes_at8. intros j Hj. rewrite length_map in Hj. exfalso. clear - Hj Hne Hlen. lia.
  - assert (Hpn2 : In (e_p g, e_n g) (ablocks B ly2 S2)).
    { destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)).
      apply in_or_app. right. exact Hine. }
    pose proof (req_size_pos (e_n g) ltac:(clear - Hn; lia)) as Hrq.
    unfold bytes_at8 in Hinb |- *. apply (GAH (e_p g) (e_n g) (e_p g));
    [exact Hpn2 | clear - Hn; lia | clear; lia | | exact Hinb].
    rewrite length_map, <- Hlen. clear - Hrq. lia. }
(* ecommon at the end of the run *)
assert (HC3 : ECOMMON g pos mf ly2 S2 W2 regs3 mem3 md3).
{ unfold ecommon.
  split; [rewrite (RK 2%bv ltac:(jw_in)); exact Rsp|].
  split; [rewrite (RK 9%bv ltac:(jw_in)); exact Rs1|].
  split; [rewrite (RK 8%bv ltac:(jw_in)); exact Rs0|].
  split; [exact Hmfb|]. split; [exact Hmf32|].
  split; [rewrite (RK 3%bv ltac:(jw_in)); exact Rgp|].
  split; [rewrite (RK 4%bv ltac:(jw_in)); exact Rtp|].
  split; [apply VMS; [clear; lia | clear - Hmfb; lia | exact V16]|].
  split; [apply VMS; [clear; lia | clear - Hmfb; lia | exact V64]|].
  split; [apply VMS; [clear; lia | clear - Hmfb; lia | exact V192]|].
  split; [apply VMS; [clear; lia | clear - Hmfb; lia | exact V168]|].
  split; [apply VMS; [clear - Hmfb; lia | clear; lia | exact Vra]|].
  split; [apply VMS; [clear - Hmfb; lia | clear; lia | exact Vs0]|].
  split; [apply VMS; [clear - Hmfb; lia | clear; lia | exact V24]|].
  split; [apply VMS; [clear - Hmfb; lia | clear; lia | exact V32]|].
  split; [apply VMS; [clear - Hmfb; lia | clear; lia | exact V40]|].
  split; [apply VMS; [clear - Hmfb; lia | clear; lia | exact V48]|].
  split; [apply VMS; [clear - Hmfb; lia | clear; lia | exact V56]|].
  split; [apply VMS; [clear - Hmfb; lia | clear; lia | exact V64b]|].
  split; [apply VMS; [clear - Hmfb; lia | clear; lia | exact V72]|].
  split; [apply VMS; [clear - Hmfb; lia | clear; lia | exact V80]|].
  split; [apply VMS; [clear - Hmfb; lia | clear; lia | exact V88]|].
  split; [apply VMS; [clear - Hmfb; lia | clear; lia | exact V96]|].
  split; [apply VMS; [clear - Hmfb; lia | clear; lia | exact V104]|].
  split; [apply VMF; [clear; lia | clear; lia | right; clear; lia | exact Vflag]|].
  split; [exact HPRE|].
  split; [intros fd; rewrite Efds; exact (Hfds fd)|].
  split; [rewrite Efs; exact Hfs | exact HINB]. }
(* jkeep at the end of the run *)
assert (HK3 : JKEEP g pos mf nm tk dp ly2 S2 W2 regs3 mem3).
{ unfold jkeep.
  split; [exact Hbl|].
  split; [unfold sh_reg; rewrite (RK 23%bv ltac:(jw_in)); exact Rs7|].
  split; [exact R24|].
  split; [rewrite (RK 21%bv ltac:(jw_in)); exact R21|].
  split; [exact W152|]. split; [exact W184|]. split; [exact W144|]. split; [exact W128|].
  split; [exact W120|]. split; [exact W176|]. split; [exact W160|]. split; [exact W112|].
  split; [exact IDK|]. exact HBUF. }
split.
- (* +0x1440: jc1 *)
  unfold jc1, acut. exists ly2, S2, regs3, mem3, md3.
  split; [reflexivity|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
  split; [exact MLE|]. split; [exact MOK|]. split; [exact HC3|].
  split; [exact HK3|]. split; [exact HID3|].
  split; [rewrite (RK 12%bv ltac:(jw_in)); exact R12|].
  split; [rewrite (RK 18%bv ltac:(jw_in)); exact R18|].
  split; [rewrite (RK 27%bv ltac:(jw_in)); exact R27|].
  split; [rewrite (RK 22%bv ltac:(jw_in)); exact R22|].
  split; [exact R25|]. split; [exact R26|].
  split; [exact ZNM|]. split; [exact ZDP|].
  split; [exact VNM|]. exact VDP.
- (* +0x1988: inv_J_end, with bad widths *)
  intros Hwf. unfold inv_J_end, acut. exists ly2, S2, regs3, mem3, md3.
  split; [reflexivity|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
  split; [exact MLE|]. split; [exact MOK|]. split; [exact HC3|].
  split; [exact Hbl|].
  split; [unfold sh_reg; rewrite (RK 23%bv ltac:(jw_in)); exact Rs7|].
  split; [exact R24|].
  split; [rewrite (RK 21%bv ltac:(jw_in)); exact R21|].
  split; [rewrite (RK 22%bv ltac:(jw_in)); exact R22|].
  split; [exact R25|]. split; [exact R26|].
  split; [exact W152|]. split; [exact W184|]. split; [exact W144|]. split; [exact W128|].
  split; [exact W120|]. split; [exact W176|]. split; [exact W160|]. split; [exact W112|].
  split; [exact ZNM|]. split; [exact ZDP|].
  split; [intros Hwt; rewrite Hwf in Hwt; discriminate Hwt|].
  intros Hr0. exfalso.
  destruct (LLVMFuzzerTestOneInput_seg_J_model.m2_fits_r0 (e_pl g) Hr0) as (Hwt & _).
  rewrite Hwf in Hwt. discriminate Hwt.
Qed.

(* x10 and x24 pinned to the literals of the case. *)
Lemma jw_pin : forall E (W : world SEGS) regs mem z10 z24,
st_ok_pi SEGS VAL E (ss_j1 0x13ec)
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x13ec)) mem (seg_rom SEGS))) ->
getr regs 10 = w64 z10 -> getr regs 24 = w64 z24 ->
st_ok_pi SEGS VAL E (ss_jw z10 z24)
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x13ec)) mem (seg_rom SEGS))).
Proof.
intros E W regs mem z10 z24 HS H10 H24.
pose proof (st_ok_pi_pin_reg' E (ss_j1 0x13ec) _ (10%bv : bv 5) z10 HS
ltac:(cbn [ms_regs restrict mkst]; exact H10) eq_refl) as HS1.
exact (st_ok_pi_pin_reg' E _ _ (24%bv : bv 5) z24 HS1
ltac:(cbn [ms_regs restrict mkst]; exact H24) eq_refl).
Qed.

(* ---- the piece ------------------------------------------------------------------------------------------- *)
Lemma j_width : j_width_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
unfold j_width_stmt. intros LAWS g pos mf nm tk dp W2 c2 Hc0.
destruct Hc0 as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HP as (HK & Hmf3 & R10 & R12 & R18 & R27 & R22).
pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & _ & _ & _ & _ & _ & _ &
_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRE & _).
pose proof HK as (Hbl & Rs7 & R24 & R21 & _).
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & H0STK & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
destruct (j_geo B LLVMF_STK LAWS g pos _ ly2 S2 W2 mem2 md2 HJ Hfrs)
as (EFa & HSF0 & HSF1 & HSF64 & Hsh0 & Hsh1 & Hsfsh).
destruct (j1_entry B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
asink_none ameta_inv arodata_okS HSTK LAWS g pos mf nm tk dp 0x13ec ly2 S2 W2 regs2 mem2 md2
HJ Hfrs HC HK Hmf3) as (HS & _ & U9 & U23 & U32).
remember (j1_E regs2 (SFa g pos) nm dp (SlotModel.t_cap_name (e_pl g)) (SlotModel.t_cap_tok (e_pl g))
(SlotModel.t_cap_disp (e_pl g)) (SlotModel.t_in (e_pl g)) (SlotModel.t_out (e_pl g))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; unfold j1_E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs2 (j1_extra (SFa g pos) nm dp (SlotModel.t_cap_name (e_pl g))
(SlotModel.t_cap_tok (e_pl g)) (SlotModel.t_cap_disp (e_pl g)) (SlotModel.t_in (e_pl g))
(SlotModel.t_out (e_pl g)))) E).
{ rewrite HE. unfold j1_E.
  split; [intros n Hn; apply Eimg_low; clear - Hn; unfold A_TEXT; lia | reflexivity]. }
clear HE.
pose proof (LLVMFuzzerTestOneInput_seg_J_model.m2_r_cases (e_pl g)) as Hrc.
unfold cfg_at. change (w64 (BASE + 0x13ec)) with (Z_to_bv 64 (BASE + 0x13ec)).
destruct (SlotModel.n_wok (e_pl g)) eqn:Hw.
- (* the widths are good: x10 = 1, and the run falls through 0x81bb0 to +0x1440 *)
  assert (P10 : getr regs2 10 = w64 1) by (rewrite R10; rewrite ?Hw; reflexivity).
  destruct Hrc as [Hr | Hr].
  + (* reac_box_name said 0 *)
    assert (P24 : getr regs2 24 = w64 0) by (rewrite R24; rewrite ?Hr; reflexivity).
    pose proof (jw_pin E W2 regs2 mem2 1 0 HS P10 P24) as HSP. clear HS.
    paj_run_to_sh RUNTOP HSP HJ 0x1440.
    { apply (jw_awr E 1 0 _ _ _ _ _ ly2 pos (SFa g pos) EFa U32 U23). }
    cbn [ms_mem mkst] in HFr.
    assert (KEEP : jw_keep W2 (SFa g pos) (shadow_addr (SFa g pos)) mem2 (ms_mem ms)).
    { intros a Ha Hw1 Hw2.
      apply (kept_of_frame E _ (w_H W2) mem2 (ms_mem ms)
      (fun x => (SFa g pos + 528 <= x < SFa g pos + 593) \/
      (shadow_addr (SFa g pos) + 66 <= x < shadow_addr (SFa g pos) + 82)) HFr);
      [| exact Ha | intros [Hx | Hx]; [exact (Hw1 Hx) | exact (Hw2 Hx)]].
      intros bb wlo whi aa Hin Hr'.
      cbn [ss_jw ss_mem windows map In j1_mf j1_sf j1_sh YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
      destruct Hin as [Eq | [Eq | [Eq | []]]]; injection Eq as <- <- <-; cbn [base_val] in Hr'.
      - clear - Hr'. lia.
      - rewrite U32 in Hr'. left. clear - Hr'. lia.
      - rewrite U23 in Hr'. right. clear - Hr'. lia. }
    pose proof (st_ok_pi_region_nth E _ _ 1 _ HSP eq_refl) as RG1.
    pose proof (st_ok_pi_region_nth E _ _ 2 _ HSP eq_refl) as RG2.
    cbn [ms_mem restrict] in RG1, RG2.
    destruct (jw_mem_facts E W2 (ms_mem ms) (SFa g pos) _ _ U32 U23 RG1 RG2
    ltac:(jw_in) ltac:(jw_in)
    ltac:(intros od Hod; cbn [In] in Hod;
    repeat (destruct Hod as [<- | Hod]; [jw_in |]); destruct Hod)) as (VNM & VDP & ZNM & ZDP).
    assert (RK : forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 12%bv; 18%bv; 21%bv; 22%bv; 23%bv; 27%bv] ->
    getr (ms_regs ms) r = getr regs2 r)
    by (eapply (regs_kept_of_st_ok_pi E _ (restrict (w_H W2) ms) regs2 _
    [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 12%bv; 18%bv; 21%bv; 22%bv; 23%bv; 27%bv] HSP HAE);
    vm_compute; reflexivity).
    prreg HSP (24%bv : bv 5) Q24. prreg HSP (25%bv : bv 5) Q25. prreg HSP (26%bv : bv 5) Q26.
    rewrite U32 in Q25, Q26.
    apply SRr_ret. pmkst HSP. left. split; [reflexivity|].
    exact (proj1 (jw_post LAWS g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _
    HJ Hfrs Hk MLE MOK HC HK Hmf3 R12 R18 R27 R22 KEEP VNM VDP ZNM ZDP RK
    ltac:(rewrite Hr; exact Q24) Q25 Q26 (j_wvb_fds md2 mat) (j_wvb_fs md2 mat))).
  + (* reac_box_name said -1 *)
    assert (P24 : getr regs2 24 = w64 (-1)) by (rewrite R24; rewrite ?Hr; reflexivity).
    pose proof (jw_pin E W2 regs2 mem2 1 (-1) HS P10 P24) as HSP. clear HS.
    paj_run_to_sh RUNTOP HSP HJ 0x1440.
    { apply (jw_awr E 1 (-1) _ _ _ _ _ ly2 pos (SFa g pos) EFa U32 U23). }
    cbn [ms_mem mkst] in HFr.
    assert (KEEP : jw_keep W2 (SFa g pos) (shadow_addr (SFa g pos)) mem2 (ms_mem ms)).
    { intros a Ha Hw1 Hw2.
      apply (kept_of_frame E _ (w_H W2) mem2 (ms_mem ms)
      (fun x => (SFa g pos + 528 <= x < SFa g pos + 593) \/
      (shadow_addr (SFa g pos) + 66 <= x < shadow_addr (SFa g pos) + 82)) HFr);
      [| exact Ha | intros [Hx | Hx]; [exact (Hw1 Hx) | exact (Hw2 Hx)]].
      intros bb wlo whi aa Hin Hr'.
      cbn [ss_jw ss_mem windows map In j1_mf j1_sf j1_sh YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
      destruct Hin as [Eq | [Eq | [Eq | []]]]; injection Eq as <- <- <-; cbn [base_val] in Hr'.
      - clear - Hr'. lia.
      - rewrite U32 in Hr'. left. clear - Hr'. lia.
      - rewrite U23 in Hr'. right. clear - Hr'. lia. }
    pose proof (st_ok_pi_region_nth E _ _ 1 _ HSP eq_refl) as RG1.
    pose proof (st_ok_pi_region_nth E _ _ 2 _ HSP eq_refl) as RG2.
    cbn [ms_mem restrict] in RG1, RG2.
    destruct (jw_mem_facts E W2 (ms_mem ms) (SFa g pos) _ _ U32 U23 RG1 RG2
    ltac:(jw_in) ltac:(jw_in)
    ltac:(intros od Hod; cbn [In] in Hod;
    repeat (destruct Hod as [<- | Hod]; [jw_in |]); destruct Hod)) as (VNM & VDP & ZNM & ZDP).
    assert (RK : forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 12%bv; 18%bv; 21%bv; 22%bv; 23%bv; 27%bv] ->
    getr (ms_regs ms) r = getr regs2 r)
    by (eapply (regs_kept_of_st_ok_pi E _ (restrict (w_H W2) ms) regs2 _
    [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 12%bv; 18%bv; 21%bv; 22%bv; 23%bv; 27%bv] HSP HAE);
    vm_compute; reflexivity).
    prreg HSP (24%bv : bv 5) Q24. prreg HSP (25%bv : bv 5) Q25. prreg HSP (26%bv : bv 5) Q26.
    rewrite U32 in Q25, Q26.
    apply SRr_ret. pmkst HSP. left. split; [reflexivity|].
    exact (proj1 (jw_post LAWS g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _
    HJ Hfrs Hk MLE MOK HC HK Hmf3 R12 R18 R27 R22 KEEP VNM VDP ZNM ZDP RK
    ltac:(rewrite Hr; exact Q24) Q25 Q26 (j_wvb_fds md2 mat) (j_wvb_fs md2 mat))).
- (* the widths are bad: x10 = 0, so reac_box_name said -1 and 0x81bb0 goes to +0x1988 *)
  assert (Hr : SlotModel.n_r (e_pl g) = -1).
  { destruct Hrc as [Hr0 | Hr1]; [|exact Hr1]. exfalso.
    destruct (LLVMFuzzerTestOneInput_seg_J_model.m2_fits_r0 (e_pl g) Hr0) as (Hwt & _).
    rewrite Hw in Hwt. discriminate Hwt. }
  assert (P10 : getr regs2 10 = w64 0) by (rewrite R10; rewrite ?Hw; reflexivity).
  assert (P24 : getr regs2 24 = w64 (-1)) by (rewrite R24; rewrite ?Hr; reflexivity).
  pose proof (jw_pin E W2 regs2 mem2 0 (-1) HS P10 P24) as HSP. clear HS.
  paj_run_to_sh RUNTOP HSP HJ 0x1988.
  { apply (jw_awr E 0 (-1) _ _ _ _ _ ly2 pos (SFa g pos) EFa U32 U23). }
  cbn [ms_mem mkst] in HFr.
  assert (KEEP : jw_keep W2 (SFa g pos) (shadow_addr (SFa g pos)) mem2 (ms_mem ms)).
  { intros a Ha Hw1 Hw2.
    apply (kept_of_frame E _ (w_H W2) mem2 (ms_mem ms)
    (fun x => (SFa g pos + 528 <= x < SFa g pos + 593) \/
    (shadow_addr (SFa g pos) + 66 <= x < shadow_addr (SFa g pos) + 82)) HFr);
    [| exact Ha | intros [Hx | Hx]; [exact (Hw1 Hx) | exact (Hw2 Hx)]].
    intros bb wlo whi aa Hin Hr'.
    cbn [ss_jw ss_mem windows map In j1_mf j1_sf j1_sh YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
    destruct Hin as [Eq | [Eq | [Eq | []]]]; injection Eq as <- <- <-; cbn [base_val] in Hr'.
    - clear - Hr'. lia.
    - rewrite U32 in Hr'. left. clear - Hr'. lia.
    - rewrite U23 in Hr'. right. clear - Hr'. lia. }
  pose proof (st_ok_pi_region_nth E _ _ 1 _ HSP eq_refl) as RG1.
  pose proof (st_ok_pi_region_nth E _ _ 2 _ HSP eq_refl) as RG2.
  cbn [ms_mem restrict] in RG1, RG2.
  destruct (jw_mem_facts E W2 (ms_mem ms) (SFa g pos) _ _ U32 U23 RG1 RG2
  ltac:(jw_in) ltac:(jw_in)
  ltac:(intros od Hod; cbn [In] in Hod;
  repeat (destruct Hod as [<- | Hod]; [jw_in |]); destruct Hod)) as (VNM & VDP & ZNM & ZDP).
  assert (RK : forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 12%bv; 18%bv; 21%bv; 22%bv; 23%bv; 27%bv] ->
  getr (ms_regs ms) r = getr regs2 r)
  by (eapply (regs_kept_of_st_ok_pi E _ (restrict (w_H W2) ms) regs2 _
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 12%bv; 18%bv; 21%bv; 22%bv; 23%bv; 27%bv] HSP HAE);
  vm_compute; reflexivity).
  prreg HSP (24%bv : bv 5) Q24. prreg HSP (25%bv : bv 5) Q25. prreg HSP (26%bv : bv 5) Q26.
  rewrite U32 in Q25, Q26.
  apply SRr_ret. pmkst HSP. right. split; [reflexivity|].
  exact (proj2 (jw_post LAWS g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _
  HJ Hfrs Hk MLE MOK HC HK Hmf3 R12 R18 R27 R22 KEEP VNM VDP ZNM ZDP RK
  ltac:(rewrite Hr; exact Q24) Q25 Q26 (j_wvb_fds md2 mat) (j_wvb_fs md2 mat)) Hw).
Qed.

Check (j_width : j_width_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).

End c.
End b.
End a.
