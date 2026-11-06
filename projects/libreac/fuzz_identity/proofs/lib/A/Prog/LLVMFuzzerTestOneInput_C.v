(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:148-161; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACja.v:107-118, for libreac/fuzz_identity's ASan build (lib/A). The same text
   also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:141-143. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_A.v; 865 of its 941 lines of code are new or changed and 504 lines of the source are left out. *)
(* Segment C of LLVMFuzzerTestOneInput's ASan walk, 0x80a7c..0x80b20 (41 slots): seg_C of
   lib/A/Prog/LLVMFuzzerTestOneInput_inv.v.

   0x80a7c calls __asan_memset on `hw` (12 bytes at SF+432; AMEMSET through YC85's aj_intrin_atS). Then
   0x80a80..0x80a88 store &id.model_name (SF+355) at mf+128, and the two guards of the record loop decide:
   0x80a8c `beqz s2` leaves for the loop's exit 0x8157c when the input is empty; otherwise the shadow test of
   the input's first byte (0x80a90..0x80aa0, with its slow path 0x82310..0x82318 for an input shorter than one
   granule), the byte itself (0x80aa8), nrec = input[0] mod 65 by the reciprocal of object 5 (0x80aac..0x80ac4,
   stored at mf+112), and 0x80ad4 `beqz a2` leaves for 0x8157c when nrec = 0. Otherwise 0x80ad8..0x80b1c set
   the loop's registers (x20 = 0, x21 = 6, x24 = SF+32) and the machine-frame slots the loop reads, and the
   run stops at the loop's head 0x80b20.

   The walk runs the engine of IdentPaLib.v on a symbolic state built at 0x80a80 from the memset's post: the
   machine frame (s1-relative, atom 9; its only writable window is [mf+32, mf+176), the slots this segment
   stores), the input's first byte (atom 26 = p), that byte's shadow cell (atom 36, named through the alias of
   p >> 3 + SHADOW_OFF), and the 8-byte constant of object 5 (the contract's HIMG). On the two guard paths
   only mf+48, mf+128 and mf+184 of the frame slots are written before 0x8157c, which inv_exit states. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YO0b YO0c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* #[local]: this flag must not leak to files that Require this one. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic states ---------------------------------------------------------------------------------- *)
(* Atoms: 0..31 the registers after the memset; 32 SHADOW_OFF; 33 SF (the class-4 frame); 34 the input's
   first byte; 35 that byte's shadow cell; 36 the cell's address SHADOW_OFF + p / 8. *)
Definition SB_C : Z := 0x7fff8000.
Definition Bx_C : sv := SOff 32 0.
Definition Bspan_C : Z * Z := (SB_C, SB_C + 2 ^ 44 - 1).
(* object 5 (0x10370): the reciprocal 0x80aac/0x80ab0 load for `% 65` *)
Definition C5 : Z := 0x03f03f03f03f03f1.
Definition mf_region : YP09.region :=
YP09.mkRegion (Some 9%nat) 0 320 32 176
[YP09.mkChunk 48 (CVal 8 (SOff 33 432)); YP09.mkChunk 80 (CVal 8 (SOff 33 0));
YP09.mkChunk 176 (CVal 8 (SOff 32 0)); YP09.mkChunk 184 (CVal 8 (SOff 33 352))].
Definition in_region : YP09.region := YP09.mkRegion (Some 26%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))].
Definition sh_region : YP09.region := YP09.mkRegion (Some 36%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 35 0))].
Definition c5_region : YP09.region := YP09.mkRegion (Some (A_OBJ 5)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit C5))].
Definition SHX : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 26 0) (SLit 3)) (SOff 32 0).
Definition cp_atoms : list (nat * afact) :=
[(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (18%nat, mkAF 1 (2 ^ 26 - 1) 0);
(26%nat, mkAF 4096 (2 ^ 47) 4); (32%nat, mkAF SB_C SB_C 0); (33%nat, mkAF 4096 (2 ^ 47) 5);
(34%nat, mkAF 0 255 0); (35%nat, mkAF 0 7 0); (36%nat, mkAF SB_C (SB_C + 2 ^ 44) 0)].
Definition cp_facts : facts := mkFacts cp_atoms [] [(SHX, SOff 36 0)].
Definition ss_cp : sstate := mkSS 0x374 sr_atoms [mf_region; in_region; sh_region; c5_region] None cp_facts.
Definition z_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
(32%nat, mkAF SB_C SB_C 0); (33%nat, mkAF 4096 (2 ^ 47) 5)] [] [].
Definition ss_z : sstate := mkSS 0x374 sr_atoms [mf_region] None z_facts.
(* The trivial state of the memset call's slot: registers only. *)
Definition ss_m : sstate := mkSS 0x370 sr_atoms [] None (mkFacts [] [] []).

(* ---- nrec: 0x80aa8..0x80ac4 compute input[0] mod 65 ------------------------------------------------------- *)
Definition NREC_SV : sv :=
SAlu ALU_SUB (SOff 34 0)
(SAlu ALU_OR (SAlu ALU_SLL (SMd M_MULHU (SOff 34 0) (SLit C5)) (SLit 6)) (SMd M_MULHU (SOff 34 0) (SLit C5))).
Definition Ek (k : Z) : env := mkEnv (fun _ => Z_to_bv 64 k) (fun _ => []).
Lemma nrec_check :
forallb (fun k => bv_eqb (sv_denot (Ek (Z.of_nat k)) NREC_SV) (Z_to_bv 64 (Z.of_nat k mod 65))) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma nrec_denot : forall E x, ew E 34 = Z_to_bv 64 x -> 0 <= x < 256 ->
sv_denot E NREC_SV = Z_to_bv 64 (x mod 65).
Proof.
intros E x Hx Hr.
assert (Hag : sv_denot E NREC_SV = sv_denot (Ek x) NREC_SV) by (unfold NREC_SV; cbn [sv_denot Ek ew]; rewrite Hx; reflexivity).
rewrite Hag. pose proof nrec_check as H. rewrite forallb_forall in H.
specialize (H (Z.to_nat x) ltac:(apply in_seq; lia)).
rewrite Z2Nat.id in H by lia.
unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq in H. exact H.
Qed.

(* ---- small facts ---------------------------------------------------------------------------------------- *)
Lemma frame_addr_le : forall n ly ly' cid pos, layout_le n ly ly' -> frame_addr ly' cid pos = frame_addr ly cid pos.
Proof. intros n ly ly' cid pos H. unfold frame_addr. destruct H as (_ & _ & _ & _ & _ & HF & _). rewrite HF. reflexivity. Qed.
Lemma div8_add : forall q j, 0 <= j < 8 -> (8 * q + j) / 8 = q.
Proof. intros q j Hj. rewrite Z.mul_comm, Z.div_add_l by lia. rewrite Z.div_small by lia. lia. Qed.
Lemma mod32_16 : forall x, x mod 32 = 0 -> x mod 16 = 0.
Proof.
intros x H. apply Z.mod_divide in H; [|lia]. apply Z.mod_divide; [lia|].
apply (Z.divide_trans _ 32); [exists 2; reflexivity | exact H].
Qed.
(* hw's two shadow cells: SF+432..439 is the first granule, SF+440..443 the first four bytes of the next. *)
Lemma hw_div0 : forall F x, F mod 32 = 0 -> F + 432 <= x < F + 440 -> x / 8 = (F + 432) / 8.
Proof.
intros F x HF Hx. pose proof (Z.div_mod F 32 ltac:(lia)) as D. rewrite HF, Z.add_0_r in D.
replace (F + 432) with (8 * (4 * (F / 32) + 54) + 0) by lia.
replace x with (8 * (4 * (F / 32) + 54) + (x - F - 432)) by lia.
rewrite !div8_add by lia. reflexivity.
Qed.
Lemma hw_div1 : forall F x, F mod 32 = 0 -> F + 440 <= x < F + 444 -> x / 8 = (F + 440) / 8 /\ x mod 8 < 4.
Proof.
intros F x HF Hx. pose proof (Z.div_mod F 32 ltac:(lia)) as D. rewrite HF, Z.add_0_r in D.
replace (F + 440) with (8 * (4 * (F / 32) + 55) + 0) by lia.
replace x with (8 * (4 * (F / 32) + 55) + (x - F - 440)) by lia.
rewrite !div8_add by lia. split; [reflexivity|].
rewrite Z.mul_comm, Z.add_comm, Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
(* The run's only write window is the machine frame's [mf+32, mf+176) (atom 9). *)
Definition c_wins_ok (rs : smem) : bool :=
forallb (fun rg => (YP09.r_whi rg <=? YP09.r_wlo rg) ||
match YP09.r_base rg with Some 9%nat => (YP09.r_wlo rg =? 32) && (YP09.r_whi rg =? 176) | _ => false end) rs.
Lemma c_nwr : forall Ex rs a mf, c_wins_ok rs = true -> bv_unsigned (ew Ex 9) = mf -> in_wrange Ex rs a ->
mf + 32 <= a < mf + 176.
Proof.
intros Ex rs a mf Hok H9 (rg & Hin & Ha). unfold c_wins_ok in Hok. rewrite forallb_forall in Hok. specialize (Hok rg Hin).
apply orb_prop in Hok. destruct Hok as [Hw | Hb].
- apply Z.leb_le in Hw. lia.
- destruct (YP09.r_base rg) as [[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]|] eqn:Eb; try discriminate Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.eqb_eq in H1, H2. cbn [base_val] in Ha. rewrite H9 in Ha. lia.
Qed.
Lemma soff_mod : forall Ex (n : nat) v c, ew Ex n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
bv_unsigned (sv_denot Ex (SOff n c)) mod 2 ^ (8 * Z.of_N 8) = v + c.
Proof.
intros Ex n v c H Hv Hvc. cbn [sv_denot]. rewrite H. rewrite (unsigned_lit_small v) by lia.
rewrite unsigned_lit_small by lia. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply Z.mod_small. lia.
Qed.
Lemma s0_dead : forall Ex s0, ew Ex 35 = Z_to_bv 64 s0 -> 0 <= s0 <= 7 ->
branch_taken BC_EQ (sv_denot Ex (SOff 35 0)) (sv_denot Ex (SLit 0)) = false ->
branch_taken BC_GE (sv_denot Ex (SLit 0)) (sv_denot Ex (SOff 35 0)) = true -> False.
Proof.
intros Ex s0 H Hs H1 H2. rewrite YO0c.branch_eq in H1. rewrite YO0c.branch_ge in H2. cbn [sv_denot] in H1, H2.
rewrite H in H1, H2.
assert (U : bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 s0) + 0)) = s0)
by (rewrite (unsigned_lit_small s0) by lia; rewrite Z.add_0_r; apply unsigned_lit_small; lia).
rewrite U in H1, H2. rewrite (unsigned_lit_small 0) in H1, H2 by lia.
unfold YO0b.s64 in H2. apply Z.eqb_neq in H1.
destruct (Z.ltb_spec 0 (2 ^ 63)); [|lia]. destruct (Z.ltb_spec s0 (2 ^ 63)); [|lia].
destruct (Z.ltb_spec 0 s0); [discriminate H2 | lia].
Qed.
Lemma nrec_br : forall Ex x, ew Ex 34 = Z_to_bv 64 x -> 0 <= x < 256 ->
branch_taken BC_EQ (sv_denot Ex NREC_SV) (sv_denot Ex (SLit 0)) = (x mod 65 =? 0).
Proof.
intros Ex x H Hx. rewrite YO0c.branch_eq, (nrec_denot Ex x H Hx).
pose proof (Z.mod_pos_bound x 65 ltac:(lia)). rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
#[local] Notation ACUT := (@acut fx rc SK PI B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation ECOMMON := (@ecommon rc PI B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation INV_B := (@inv_B_end fx rc SK PI B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation INV_REC := (@inv_rec fx rc SK PI B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation INV_EXIT := (@inv_exit fx rc SK PI B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation SEG_C := (@seg_C fx rc SK PI B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation HBLOCKS := (@hblocks rc PI B).

(* The run's needs of the contract's constants and the image (LLVMFuzzerTestOneInput.v's Section). *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA IS___asan_memset).
(* The image constants, as the contract takes them (LLVMFuzzerTestOneInput.v llvmf_img, HIMG): this segment reads
   the first, the reciprocal 0x03f03f03f03f03f1 at object 5 (0x10370). *)
Variable G : list (Z * Z).
Hypothesis HIMG : forall (W : world SEGS) mem,
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> llvmf_img B G W mem.
(* cgif ACfh.v:162-164, as LLVMFuzzerTestOneInput.v takes it: the walk's journal keeps the fds and the fs. *)
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* The machine state after the memset: what the rest of the segment needs of it. *)
Definition C_mid (g : ectx) (pos mf : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS)
(regs2 : bvmap 5 word) (mem2 : word -> option byte) (c3 : config) : Prop :=
exists regs3 mem3 md3,
c3 = cfg_at SEGS (BASE + 0x374) regs3 mem3 md3 /\
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly2 S2 W2 mem3 md3 0 /\
(forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 26]%bv -> getr regs3 r = getr regs2 r) /\
(forall i, 0 <= i < 12 -> aview SEGS (w_H W2) mem3 (SFa g pos + V_hw + i) = Some 0) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (SFa g pos + V_hw <= a < SFa g pos + V_hw + 12) -> ~ (mf - ESTACK <= a < mf) ->
aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a).

Lemma C_memset : forall g pos mf ly2 S2 W2 regs2 mem2 md2,
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly2 S2 W2 mem2 md2 0 ->
frames S2 = [(4, pos)] ->
ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 10 = w64 (SFa g pos + V_hw) -> getr regs2 11 = w64 0 -> getr regs2 12 = w64 12 ->
aview SEGS (w_H W2) mem2 (shadow_addr (SFa g pos + V_hw)) = Some 0 ->
aview SEGS (w_H W2) mem2 (shadow_addr (SFa g pos + V_hw + 8)) = Some 4 ->
SRr SEGS W2 (cfg_at SEGS (BASE + 0x370) regs2 mem2 md2) (fun W3 c3 => W3 = W2 /\ C_mid g pos mf ly2 S2 W2 regs2 mem2 c3).
Proof.
intros g pos mf ly2 S2 W2 regs2 mem2 md2 HJ HFR HEC R10 R11 R12 HSH0 HSH4.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
destruct HEC as (R2 & R9 & R8 & HMF & HMF32 & R3 & R4 & R19 & _).
remember (Eimg (Ereg regs2 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HS : st_ok_pi SEGS VAL E ss_m (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x370)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_m. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- exact I.
- split; [exact I | split; exact I]. }
assert (SHOK : sh_ok SEGS Bx_C [] E (mrestrict (w_H W2) mem2)) by constructor.
unfold cfg_at. change (w64 (BASE + 0x370)) with (Z_to_bv 64 (BASE + 0x370)).
paj_run_tok RUN HS HJ SHOK Bspan_C; [apply awr_ok_nil |].
assert (HAE : env_agree 32 (Ereg regs2 []) E)
by (split; [intros n Hn; subst E; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Hmem : forall a, aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a. apply aview_eq_of. apply HFr. intros (rr & Hin & _). destruct Hin. }
clear HF HFr HG SHOK.
pose proof (regs_kept_of_st_ok SEGS E _ (restrict (w_H W2) ms) regs2 [] [2; 3; 4; 8; 9; 18; 19; 26]%bv HS HAE
ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
rewrite (EE 10%nat 10%bv eq_refl), R10 in Q10. rewrite (EE 11%nat 11%bv eq_refl), R11 in Q11. rewrite (EE 12%nat 12%bv eq_refl), R12 in Q12.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (Hfin : In (4, pos) (frames S2)) by (rewrite HFR; left; reflexivity).
pose proof (frame_addr_le _ _ _ 4 pos Hly) as HFeq. fold (SFa g pos) in HFeq.
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HAR Hfin) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR Hfin) as (HF4096 & HFceil & _).
rewrite HFeq in HFal, HFapp, HFpres, HFSpres, HF4096, HFceil.
change (fs_frame_bytes 4) with 1024 in HFapp, HFpres, HFSpres, HFceil.
set (F := SFa g pos) in *.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5').
unfold STK_LLVMF, ESTACK, ASTACK in HSTK.
assert (Rmf : spZ (ms_regs ms) = mf).
{ unfold spZ. rewrite (HKR 2%bv ltac:(cbn; tauto)), R2. unfold w64. rewrite unsigned_lit_small; [reflexivity|]. clear - HMF Hslo Hshi Hceil H47 C1 HSTK. lia. }
pmkst HS.
eapply SRr_bind.
{ apply (aj_intrin_atS SEGS B LAWS Hsegs OSet (SIGMA IS___asan_memset) AMEMSET W2 (ms_regs ms) (ms_mem ms)
LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 _ 0 (F + V_hw) 0 12
(mf - e_sp0 g) (Z_to_bv 64 (BASE + 884)) HJ Q10 Q11 Q12).
- lia.
- unfold V_hw. clear - HF4096. lia.
- unfold V_hw. clear - HFceil C1. lia.
- rewrite Rmf. lia.
- clear - HMF32 Hal16. rewrite Zminus_mod, (mod32_16 mf HMF32), Hal16. reflexivity.
- clear - HMF. lia.
- unfold ESTACK. clear - HMF HSTK. lia.
- rewrite (HKR 3%bv ltac:(cbn; tauto)). exact R3.
- rewrite (HKR 4%bv ltac:(cbn; tauto)). exact R4.
- exact Q1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a Ha. unfold V_hw in Ha. split.
+ right; right; right. exists 4, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
rewrite HFeq. change (fs_frame_bytes 4) with 1024. fold F. clear - Ha. lia.
+ unfold ESTACK. clear - Ha HFceil Hceil Hslo HMF HSTK. lia.
- apply (amem_range_sub_app F 1024 (F + V_hw) 12); [exact HFapp | exact HFceil | unfold V_hw; lia | unfold V_hw; lia | lia].
- intros x Hx. rewrite Hmem. unfold shadow_of_addr. unfold V_hw in Hx, HSH0, HSH4.
destruct (Z_lt_ge_dec x (F + 440)) as [Hlo | Hhi].
+ exists 0. split; [| left; reflexivity]. rewrite (hw_div0 F x HFal ltac:(lia)). exact HSH0.
+ destruct (hw_div1 F x HFal ltac:(lia)) as [Hq Hm]. exists 4. split; [| right; lia].
rewrite Hq. replace (F + 432 + 8) with (F + 440) in HSH4 by lia. exact HSH4.
- intros _ s Hs. unfold shadow_addr, V_hw, SHADOW_OFF in Hs.
pose proof (Z.div_mod F 32 ltac:(lia)) as DF. rewrite HFal, Z.add_0_r in DF.
assert (E1 : (2147450880 + (F + 432) / 8) / 8 * 8 >= 2147450880 + F / 8 + 47).
{ replace (F + 432) with (8 * (4 * (F / 32) + 54) + 0) by lia. rewrite div8_add by lia.
replace F with (8 * (4 * (F / 32)) + 0) at 2 by lia. rewrite div8_add by lia.
pose proof (Z.mul_div_le (2147450880 + (4 * (F / 32) + 54)) 8 ltac:(lia)) as M1.
pose proof (Z.mod_pos_bound (2147450880 + (4 * (F / 32) + 54)) 8 ltac:(lia)) as M2.
pose proof (Z.div_mod (2147450880 + (4 * (F / 32) + 54)) 8 ltac:(lia)) as M3. lia. }
assert (E2 : (2147450880 + (F + 432 + 12 - 1) / 8) / 8 * 8 + 8 <= 2147450880 + F / 8 + 64).
{ replace (F + 432 + 12 - 1) with (8 * (4 * (F / 32) + 55) + 3) by lia. rewrite div8_add by lia.
replace F with (8 * (4 * (F / 32)) + 0) at 2 by lia. rewrite div8_add by lia.
pose proof (Z.mul_div_le (2147450880 + (4 * (F / 32) + 55)) 8 ltac:(lia)) as M1. lia. }
apply (aview_some_of_apresent SEGS).
replace s with (shadow_addr F + (s - shadow_addr F)) by lia.
apply (HFSpres (s - shadow_addr F)). unfold shadow_addr, SHADOW_OFF. change (1024 / 8) with 128. lia.
- exact I. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Heff & Hfr3 & Hpres3 & Hsame3).
apply SRr_ret. split; [reflexivity|]. exists regs3, mem3, md3.
split; [reflexivity|]. split; [exact HJ3|]. split.
{ intros r Hr. rewrite <- (HKR r Hr). pose proof (HP3 (bv_unsigned r)) as Hq. rewrite Z_to_bv_bv_unsigned in Hq. apply Hq.
cbn [In] in Hr.
repeat (destruct Hr as [<- | Hr];
[lazymatch goal with |- acallee_saved (bv_unsigned ?x) => let v := eval vm_compute in (bv_unsigned x) in
change (bv_unsigned x) with v end; unfold acallee_saved; lia |]). destruct Hr. }
split.
{ intros i Hi. fold F. rewrite (Heff i Hi). reflexivity. }
intros a Ha Hhw Hwin. rewrite (Hfr3 a Ha Hhw); [exact (Hmem a) |]. clear - Hwin. intros H. apply Hwin. lia.
Qed.

(* ---- the symbolic state at 0x80a80 ------------------------------------------------------------------------ *)
Definition EC (regs : bvmap 5 word) (F x0 s0 p : Z) : env :=
Eimg (Ereg regs (map (Z_to_bv 64) [SB_C; F; x0; s0; SB_C + p / 8])).
Definition EZ (regs : bvmap 5 word) (F : Z) : env := Eimg (Ereg regs (map (Z_to_bv 64) [SB_C; F])).
Lemma val_mem1_of_aview : forall H mem a v, aview SEGS H mem a = Some v -> val_mem SEGS (mrestrict H mem) a 1 v.
Proof.
intros H mem a v Hv j Hj. assert (j = 0%nat) by lia. subst j. rewrite Z.add_0_r.
destruct (aview_byte SEGS H mem a v Hv) as (b & Hb & -> & Hr). rewrite Hb. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, YO0f.le_byte. change (bv_modulus 8) with 256.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
rewrite !(Z.mod_small (bv_unsigned b) 256 Hr). reflexivity.
Qed.
Lemma val_mem_keep : forall H (m m' : word -> option byte) a n v,
(forall k, (k < n)%nat -> aview SEGS H m' (a + Z.of_nat k) = aview SEGS H m (a + Z.of_nat k)) ->
val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v.
Proof. intros H m m' a n v Hk Hv k Hlt. rewrite (mbyte_of_aview SEGS H H m m' (a + Z.of_nat k) (Hk k Hlt)). exact (Hv k Hlt). Qed.
Lemma mf_region_ok : forall E mf F (W : world SEGS) mem,
bv_unsigned (ew E 9) = mf -> ew E 32 = Z_to_bv 64 SB_C -> ew E 33 = Z_to_bv 64 F ->
0 <= mf -> mf + 320 <= 2 ^ 64 -> 0 <= F -> F + 432 < 2 ^ 64 ->
(forall o, 32 <= o < 176 -> apresent (w_H W) mem (mf + o)) ->
val_mem SEGS (rd W mem) (mf + 48) 8 (F + 432) -> val_mem SEGS (rd W mem) (mf + 80) 8 F ->
val_mem SEGS (rd W mem) (mf + 176) 8 SHADOW_OFF -> val_mem SEGS (rd W mem) (mf + 184) 8 (F + 352) ->
region_ok SEGS E (rd W mem) mf_region.
Proof.
intros E mf F W mem H9 H32 H33 Hm0 Hm1 HF0 HF1 Hpres M48 M80 M176 M184.
unfold region_ok, mf_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite H9. split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres; lia|].
repeat apply Forall_cons; try apply Forall_nil.
- apply (chunk_ok_val SEGS E _ mf 48 8 (SOff 33 432) (F + 432));
[cbn [sv_denot]; rewrite H33, unsigned_lit_small by lia; reflexivity | zside | zside | exact M48].
- apply (chunk_ok_val SEGS E _ mf 80 8 (SOff 33 0) F);
[cbn [sv_denot]; rewrite H33, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity | zside | zside | exact M80].
- apply (chunk_ok_val SEGS E _ mf 176 8 (SOff 32 0) SB_C);
[cbn [sv_denot]; rewrite H32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB_C; zside | zside | exact M176].
- apply (chunk_ok_val SEGS E _ mf 184 8 (SOff 33 352) (F + 352));
[cbn [sv_denot]; rewrite H33, unsigned_lit_small by lia; reflexivity | zside | zside | exact M184].
Qed.
Lemma C_entry_pos : forall g pos mf ly2 S2 W2 mem3 md3 (regs3 : bvmap 5 word),
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly2 S2 W2 mem3 md3 0 ->
frames S2 = [(4, pos)] ->
getr regs3 2 = w64 mf -> getr regs3 9 = w64 mf -> getr regs3 18 = w64 (e_n g) -> getr regs3 26 = w64 (e_p g) ->
e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
0 < e_n g < 2 ^ 26 -> In (e_p g, e_n g) (ablocks B ly2 S2) ->
val_mem SEGS (rd W2 mem3) (mf + 48) 8 (SFa g pos + V_hw) ->
val_mem SEGS (rd W2 mem3) (mf + 80) 8 (SFa g pos) ->
val_mem SEGS (rd W2 mem3) (mf + 176) 8 SHADOW_OFF ->
val_mem SEGS (rd W2 mem3) (mf + 184) 8 (SFa g pos + V_id) ->
val_mem SEGS (rd W2 mem3) (e_p g) 1 (SlotModel.inb (e_pl g) 0) ->
val_mem SEGS (rd W2 mem3) (VAL (A_OBJ 5)) 8 C5 ->
st_ok_pi SEGS VAL (EC regs3 (SFa g pos) (SlotModel.inb (e_pl g) 0) (if 0 <? e_n g / 8 then 0 else e_n g mod 8) (e_p g))
ss_cp (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 (BASE + 0x374)) mem3 (seg_rom SEGS))).
Proof.
intros g pos mf ly2 S2 W2 mem3 md3 regs3 HJ HFR R2 R9 R18 R26 HMF HMF32 Hn Hin M48 M80 M176 M184 MX0 MC5.
set (F := SFa g pos) in *. set (p := e_p g) in *. set (n := e_n g) in *.
set (x0 := SlotModel.inb (e_pl g) 0) in *. set (s0 := if 0 <? n / 8 then 0 else n mod 8).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (Hfin : In (4, pos) (frames S2)) by (rewrite HFR; left; reflexivity).
pose proof (frame_addr_le _ _ _ 4 pos Hly) as HFeq. fold (SFa g pos) F in HFeq.
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HAR Hfin) as (HFal & _ & _ & _).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR Hfin) as (HF4096 & HFceil & _).
rewrite HFeq in HFal, HF4096, HFceil. change (fs_frame_bytes 4) with 1024 in HFceil.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (Hp16 & Hp4096 & Hpceil & Happ & _).
pose proof (blk_off_imgP B _ _ _ _ _ p n HAR Hin) as Hpimg.
pose proof (req_size_pos0 n ltac:(lia)) as Hreq.
destruct (al_shadow _ _ LAWS _ _ _ _ _ p n HAR Hin) as [Hbs _].
assert (Hs0 : aview SEGS (w_H W2) mem3 (SB_C + p / 8) = Some s0).
{ destruct Hbs as (_ & _ & Hbs). specialize (Hbs 0 ltac:(split; [lia|]; apply Z.div_str_pos; lia)).
unfold shadow_of_addr in Hbs. rewrite Z.add_0_r in Hbs. change SB_C with SHADOW_OFF. rewrite Hbs. subst s0. unfold req_size.
destruct (Z.eqb_spec n 0); [lia|]. reflexivity. }
assert (Rs0 : 0 <= s0 <= 7) by (subst s0; destruct (0 <? n / 8); [lia | pose proof (Z.mod_pos_bound n 8 ltac:(lia)); lia]).
assert (Rx0 : 0 <= x0 < 256) by (subst x0; unfold SlotModel.inb, RcIdentModel.bz; apply (bv_unsigned_in_range 8)).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5').
unfold STK_LLVMF, ESTACK, ASTACK in HSTK.
pose proof (pa_obj_img 5 ltac:(lia)) as H5.
assert (Rmf : alloc_ceiling <= mf /\ 2 ^ 46 <= mf /\ mf + 320 <= 2 ^ 47) by (clear - HMF Hslo Hshi Hceil H47 C1 HSTK; lia).
pose proof (Z.div_mod p 8 ltac:(lia)) as Dp8. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Mp8.
rewrite restrict_mkst_fx.
set (E := EC regs3 F x0 s0 p).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs3 (map (Z_to_bv 64) [SB_C; F; x0; s0; SB_C + p / 8])) k)
by (intros k Hk; subst E; unfold EC; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = w64 mf) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl); exact R2).
assert (E9 : ew E 9 = w64 mf) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 9 9%bv eq_refl); exact R9).
assert (E18 : ew E 18 = w64 n) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 18 18%bv eq_refl); exact R18).
assert (E26 : ew E 26 = w64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 26 26%bv eq_refl); exact R26).
assert (E32 : ew E 32 = Z_to_bv 64 SB_C) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 F) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 x0) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 s0) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (SB_C + p / 8)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 4)).
assert (EO5 : ew E (A_OBJ 5) = Z_to_bv 64 (VAL (A_OBJ 5))) by (subst E; unfold EC; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v).
{ intros k v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
pose proof (pa_val_range (A_OBJ 5)) as R5.
unfold ss_cp. apply pa_entry_st_ok_full.
- subst E. unfold EC. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
+ apply (mf_region_ok E mf F W2 mem3);
[rewrite E9; unfold w64; apply unsigned_lit_small; lia | exact E32 | exact E33 | lia | lia | lia | lia
| intros o Ho; apply Hpres; clear - Ho HMF HSTK; lia | exact M48 | exact M80 | exact M176 | exact M184].
+ unfold region_ok, in_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite (VB 26%nat p E26) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ p 0 1 (SOff 34 0) x0);
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact MX0.
+ unfold region_ok, sh_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite (VB 36%nat (SB_C + p / 8) E36) by (unfold SB_C; lia). split; [unfold SB_C; lia|]. split; [unfold SB_C; lia|].
split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (SB_C + p / 8) 0 1 (SOff 35 0) s0);
[cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem1_of_aview _ _ _ _ Hs0).
+ unfold region_ok, c5_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite (VB (A_OBJ 5) (VAL (A_OBJ 5)) EO5) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 5)) 0 8 (SLit C5) C5); [reflexivity | unfold C5; zside | zside |].
rewrite Z.add_0_r. exact MC5.
- apply pairwise_disjoint_of_extents.
unfold mf_region, in_region, sh_region, c5_region, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB 9%nat mf E9) by lia. rewrite (VB 26%nat p E26) by lia.
rewrite (VB 36%nat (SB_C + p / 8) E36) by (unfold SB_C; lia). rewrite (VB (A_OBJ 5) (VAL (A_OBJ 5)) EO5) by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold SB_C.
clear - Rmf Hp4096 Hpceil Happ Hpimg Hreq H5 C1 Dp8 Mp8 Hceil.
repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [cp_facts cp_atoms f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E18, E26, E32, E33, E34, E35, E36. unfold w64.
rewrite !unsigned_lit_small by (unfold SB_C; lia).
change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
unfold SB_C. clear - Rmf HMF32 Hn Hp16 Hp4096 Hpceil Hreq HF4096 HFceil HFal Rx0 Rs0 Dp8 Mp8 C1.
repeat match goal with |- _ /\ _ => split end; try lia.
+ split; [|exact I]. cbn [cp_facts f_alias]. unfold SHX.
apply (shadow_decl_ok E 26 32 36 p SB_C); [rewrite E26; reflexivity | lia | exact E32 | exact E36].
Qed.
Lemma C_entry_zero : forall g pos mf ly2 S2 W2 mem3 md3 (regs3 : bvmap 5 word),
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly2 S2 W2 mem3 md3 0 ->
frames S2 = [(4, pos)] ->
getr regs3 2 = w64 mf -> getr regs3 9 = w64 mf ->
e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
val_mem SEGS (rd W2 mem3) (mf + 48) 8 (SFa g pos + V_hw) ->
val_mem SEGS (rd W2 mem3) (mf + 80) 8 (SFa g pos) ->
val_mem SEGS (rd W2 mem3) (mf + 176) 8 SHADOW_OFF ->
val_mem SEGS (rd W2 mem3) (mf + 184) 8 (SFa g pos + V_id) ->
st_ok_pi SEGS VAL (EZ regs3 (SFa g pos)) ss_z
(restrict (w_H W2) (mkst regs3 (Z_to_bv 64 (BASE + 0x374)) mem3 (seg_rom SEGS))).
Proof.
intros g pos mf ly2 S2 W2 mem3 md3 regs3 HJ HFR R2 R9 HMF HMF32 M48 M80 M176 M184.
set (F := SFa g pos) in *.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (Hfin : In (4, pos) (frames S2)) by (rewrite HFR; left; reflexivity).
pose proof (frame_addr_le _ _ _ 4 pos Hly) as HFeq. fold (SFa g pos) F in HFeq.
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HAR Hfin) as (HFal & _ & _ & _).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR Hfin) as (HF4096 & HFceil & _).
rewrite HFeq in HFal, HF4096, HFceil. change (fs_frame_bytes 4) with 1024 in HFceil.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5').
unfold STK_LLVMF, ESTACK, ASTACK in HSTK.
assert (Rmf : alloc_ceiling <= mf /\ 2 ^ 46 <= mf /\ mf + 320 <= 2 ^ 47) by (clear - HMF Hslo Hshi Hceil H47 C1 HSTK; lia).
rewrite restrict_mkst_fx.
set (E := EZ regs3 F).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs3 (map (Z_to_bv 64) [SB_C; F])) k)
by (intros k Hk; subst E; unfold EZ; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = w64 mf) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl); exact R2).
assert (E9 : ew E 9 = w64 mf) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 9 9%bv eq_refl); exact R9).
assert (E32 : ew E 32 = Z_to_bv 64 SB_C) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 F) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
unfold ss_z. apply pa_entry_st_ok_full.
- subst E. unfold EZ. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
apply (mf_region_ok E mf F W2 mem3);
[rewrite E9; unfold w64; apply unsigned_lit_small; lia | exact E32 | exact E33 | lia | lia | lia | lia
| intros o Ho; apply Hpres; clear - Ho HMF HSTK; lia | exact M48 | exact M80 | exact M176 | exact M184].
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [|split; exact I].
cbn [z_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E32, E33. unfold w64. rewrite !unsigned_lit_small by (unfold SB_C; lia).
change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
unfold SB_C. clear - Rmf HMF32 HF4096 HFceil HFal C1.
repeat match goal with |- _ /\ _ => split end; try lia.
Qed.

(* ---- the boundary at the end ------------------------------------------------------------------------------ *)
(* What the segment writes: hw (the memset), the memset's scratch window below sp, and the machine-frame slots
   0x80a88..0x80b1c store (the window of mf_region). *)
Definition cwin (F mf a : Z) : Prop := (F + 432 <= a < F + 444) \/ (mf - ESTACK <= a < mf) \/ (mf + 32 <= a < mf + 176).
Lemma val_mem_zero_of_aview : forall H mem a n, (forall k, (k < n)%nat -> aview SEGS H mem (a + Z.of_nat k) = Some 0) ->
val_mem SEGS (mrestrict H mem) a n 0.
Proof.
intros H mem a n Hz k Hk. destruct (aview_byte SEGS H mem (a + Z.of_nat k) 0 (Hz k Hk)) as (b & Hb & Hv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, <- Hv. unfold bv_wrap, YO0f.le_byte.
rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity.
Qed.
Lemma garr8_keep : forall H (m m' : word -> option byte) a l,
(forall j, (j < length l)%nat -> aview SEGS H m' (a + Z.of_nat j) = aview SEGS H m (a + Z.of_nat j)) ->
garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H m') a l.
Proof.
intros H m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_keep H m m'); [|exact Hv]. intros k Hk1. assert (k = 0%nat) by lia. subst k. rewrite Z.add_0_r. exact (Hk j Hj).
Qed.
(* The layout facts every kept address uses: the side frame, the machine frame, the stack. *)
Lemma C_layout : forall g pos mf ly2 S2 W2 mem2 md2,
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly2 S2 W2 mem2 md2 0 ->
frames S2 = [(4, pos)] -> e_sp0 g - 336 <= mf <= e_sp0 g - 320 ->
SFa g pos mod 32 = 0 /\ 4096 <= SFa g pos /\ SFa g pos + 1024 <= alloc_ceiling /\ in_app (SFa g pos) 1024 /\
alloc_ceiling + 12000 <= mf /\ mf + 320 <= e_sp0 g /\ e_sp0 g <= 2 ^ 47 /\ 140735332483072 <= alloc_ceiling /\
e_sp0 g - LLVMF_STK <= mf - ESTACK /\ frame_addr ly2 4 pos = SFa g pos.
Proof.
intros g pos mf ly2 S2 W2 mem2 md2 HJ HFR HMF.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (Hfin : In (4, pos) (frames S2)) by (rewrite HFR; left; reflexivity).
pose proof (frame_addr_le _ _ _ 4 pos Hly) as HFeq. fold (SFa g pos) in HFeq.
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HAR Hfin) as (HFal & HFapp & _ & _).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR Hfin) as (HF4096 & HFceil & _).
rewrite HFeq in HFal, HFapp, HF4096, HFceil. change (fs_frame_bytes 4) with 1024 in HFapp, HFceil.
pose proof (asan_consts) as (C1 & _).
unfold STK_LLVMF, ESTACK, ASTACK in HSTK. unfold ESTACK.
split; [exact HFal|]. split; [exact HF4096|]. split; [exact HFceil|]. split; [exact HFapp|].
split; [clear - HMF Hceil Hslo HSTK; lia|]. split; [clear - HMF; lia|]. split; [clear - Hshi H47; lia|].
split; [clear - C1; lia|]. split; [clear - HMF HSTK; lia|]. exact HFeq.
Qed.
(* ecommon, id at 0 and hw at 0 at the end of the segment, from the start and what the segment wrote. *)
Lemma C_keep : forall g pos mf ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4,
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly2 S2 W2 mem2 md2 0 ->
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly2 S2 W2 mem4 md4 0 ->
frames S2 = [(4, pos)] -> HBLOCKS g ly2 S2 [] ->
ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
id_at g pos 0 W2 mem2 ->
aview SEGS (w_H W2) mem2 (shadow_addr (SFa g pos + V_hw)) = Some 0 ->
aview SEGS (w_H W2) mem2 (shadow_addr (SFa g pos + V_hw + 8)) = Some 4 ->
(forall r : bv 5, In r [2; 3; 4; 8; 9; 19]%bv -> getr regs4 r = getr regs2 r) ->
(forall i, 0 <= i < 12 -> aview SEGS (w_H W2) mem4 (SFa g pos + V_hw + i) = Some 0) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ cwin (SFa g pos) mf a -> aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W2) mem2 a) ->
val_mem SEGS (rd W2 mem4) (mf + 80) 8 (SFa g pos) ->
ECOMMON g pos mf ly2 S2 W2 regs4 mem4 md4 /\ id_at g pos 0 W2 mem4 /\ hw_at g pos 0 W2 mem4.
Proof.
intros g pos mf ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4 HJ2 HJ4 HFR HBL HEC HID HSH0 HSH4 HR HZ KEEP M80.
pose proof HEC as (R2 & R9 & R8 & HMF & HMF32 & R3 & R4 & R19 & M80' & M192 & M176 & Mra & Ms0 & W24 & W32 & W40 & W48 & W56
& W64 & W72 & W80 & W88 & W96 & W104 & M24 & MFL & HPRE & HFD & HFS & HBY).
destruct (C_layout g pos mf ly2 S2 W2 mem2 md2 HJ2 HFR HMF) as (HFal & HF4096 & HFceil & HFapp & Hmf1 & Hmf2 & Hsp47 & C1 & Hwin & HFeq).
set (F := SFa g pos) in *.
pose proof (Z.div_mod F 32 ltac:(lia)) as DF. rewrite HFal, Z.add_0_r in DF.
assert (DF8 : F / 8 = 4 * (F / 32)) by (rewrite DF at 1; replace (32 * (F / 32)) with (8 * (4 * (F / 32)) + 0) by lia; apply div8_add; lia).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
(* a word of the machine stack above the frame's slots, or of the side frame outside hw, is kept *)
assert (KMS : forall a v, mf + 176 <= a -> a + 8 <= e_sp0 g ->
val_mem SEGS (rd W2 mem2) a 8 v -> val_mem SEGS (rd W2 mem4) a 8 v).
{ intros a v Ha1 Ha2 Hv. apply (val_mem_keep (w_H W2) mem2 mem4); [|exact Hv]. intros k Hk. apply KEEP; [lia|].
unfold cwin, ESTACK. clear - Ha1 Ha2 Hk Hmf1 HFceil. lia. }
assert (KF : forall a n v, F <= a -> a + Z.of_nat n <= F + 432 \/ F + 444 <= a -> a + Z.of_nat n <= F + 1024 ->
val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 mem4) a n v).
{ intros a n v Ha1 Ha2 Ha3 Hv. apply (val_mem_keep (w_H W2) mem2 mem4); [|exact Hv]. intros k Hk. apply KEEP; [lia|].
unfold cwin, ESTACK. clear - Ha1 Ha2 Ha3 Hk Hmf1 HFceil. lia. }
(* a shadow cell of the side frame is kept *)
assert (KSH : forall c, 0 <= c < 128 -> aview SEGS (w_H W2) mem4 (SHADOW_OFF + F / 8 + c) = aview SEGS (w_H W2) mem2 (SHADOW_OFF + F / 8 + c)).
{ intros c Hc. apply KEEP; [unfold SHADOW_OFF; clear - Hc DF DF8 HF4096 HFceil Hmf1 Hmf2 Hsp47; lia|].
unfold cwin, ESTACK, SHADOW_OFF. clear - Hc HFapp Hmf1 Hmf2 Hsp47 HFceil DF DF8 C1. lia. }
assert (D8 : forall c, 0 <= c -> (F + 8 * c) / 8 = F / 8 + c).
{ intros c Hc. rewrite DF8. rewrite DF at 1. replace (32 * (F / 32) + 8 * c) with (8 * (4 * (F / 32) + c) + 0) by lia.
apply div8_add. lia. }
assert (SHI : forall c i, 0 <= c -> 0 <= i -> c + i < 128 ->
aview SEGS (w_H W2) mem4 (shadow_of_addr SHADOW_OFF (F + 8 * c) + i) = aview SEGS (w_H W2) mem2 (shadow_of_addr SHADOW_OFF (F + 8 * c) + i)).
{ intros c i Hc Hi Hci. unfold shadow_of_addr. rewrite (D8 c Hc).
replace (SHADOW_OFF + (F / 8 + c) + i) with (SHADOW_OFF + F / 8 + (c + i)) by lia. apply KSH. lia. }
split; [|split].
- unfold ecommon.
rewrite (HR 2%bv ltac:(cbn; tauto)), (HR 9%bv ltac:(cbn; tauto)), (HR 8%bv ltac:(cbn; tauto)),
(HR 3%bv ltac:(cbn; tauto)), (HR 4%bv ltac:(cbn; tauto)), (HR 19%bv ltac:(cbn; tauto)).
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as [Hfd2 Hfs2].
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as [Hfd4 Hfs4].
do 8 (split; [assumption|]).
split; [exact M80|].
split; [apply KMS; [lia | lia | exact M192]|].
split; [apply KMS; [lia | lia | exact M176]|].
do 13 (split; [apply KMS; [lia | lia | assumption]|]).
split.
{ apply (val_mem_keep (w_H W2) mem2 mem4); [|exact M24]. intros k Hk. apply KEEP; [lia|].
unfold cwin, ESTACK. clear - Hk Hmf1 HFceil. lia. }
split; [apply (KF (F + 1016) 8%nat); [lia | cbn; lia | cbn; lia | exact MFL]|].
split; [exact HPRE|].
split; [intros fd; rewrite Hfd4; reflexivity|].
split; [exact Hfs4|].
(* the input block: a heap block of the entry, apart from the frame and the stack *)
pose proof HPRE as (_ & _ & _ & _ & HINP & HLEN & _).
unfold bytes_at8 in *. apply (garr8_keep (w_H W2) mem2 mem4); [|exact HBY].
intros j Hj. rewrite length_map in Hj. assert (Hj' : 0 <= Z.of_nat j < e_n g) by (rewrite HLEN; lia).
destruct HINP as [(Hn0 & _) | (Hnp & Hin)]; [lia|].
pose proof HJ2 as (HAR & _).
assert (Hin2 : In (e_p g, e_n g) (ablocks B ly2 S2)) by (destruct HBL as [HP _]; apply (Permutation_in _ (Permutation_sym HP)); exact Hin).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin2) as (_ & Hp4096 & Hpceil & _).
pose proof (req_size_pos0 (e_n g) ltac:(lia)) as Hreq.
assert (Hfin : In (4, pos) (frames S2)) by (rewrite HFR; left; reflexivity).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ 4 pos HAR Hin2 Hfin) as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite HFeq in Hsep. change (fs_frame_bytes 4) with 1024 in Hsep.
apply KEEP; [clear - Hj' Hp4096 Hpceil Hreq Hmf1 Hmf2 Hsp47; lia|].
unfold cwin, ESTACK. clear - Hj' Hsep Hreq Hpceil Hmf1 HFceil. lia.
- destruct HID as (HIDB & HIDS & HIDK). split; [|split].
+ unfold bytes_at8 in *. apply (garr8_keep (w_H W2) mem2 mem4); [|exact HIDB].
intros j Hj. rewrite length_map in Hj. unfold m_id in Hj. rewrite SlotModel.rec_id_length in Hj. unfold RcIdentModel.ID_SIZE in Hj.
unfold V_id. apply KEEP; [clear - Hj HF4096 HFceil Hmf1 Hmf2 Hsp47; lia|]. unfold cwin, ESTACK. clear - Hj Hmf1 HFceil. lia.
+ unfold sh_zero, zero_shadow in *. intros i Hi. change (N_id / 8) with 4 in Hi.
rewrite <- (HIDS i ltac:(change (N_id / 8) with 4; lia)). unfold V_id. fold F.
replace (F + 352) with (F + 8 * 44) by lia. apply SHI; lia.
+ unfold sh_blk, block_shadow in *. destruct HIDK as (HK1 & HK2 & HK3'). split; [exact HK1|]. split; [exact HK2|].
intros i Hi. rewrite <- (HK3' i Hi). unfold N_id in Hi. change ((38 + 7) / 8) with 5 in Hi. unfold V_id. fold F.
replace (F + 352) with (F + 8 * 44) by lia. apply SHI; lia.
- unfold shadow_addr, V_hw in HSH0, HSH4. fold F in HSH0, HSH4.
replace (SHADOW_OFF + (F + 432) / 8) with (shadow_of_addr SHADOW_OFF (F + 8 * 54) + 0) in HSH0
by (unfold shadow_of_addr; rewrite (D8 54) by lia; replace (F + 432) with (F + 8 * 54) by lia; rewrite (D8 54) by lia; lia).
replace (SHADOW_OFF + (F + 432 + 8) / 8) with (shadow_of_addr SHADOW_OFF (F + 8 * 54) + 1) in HSH4
by (unfold shadow_of_addr; rewrite (D8 54) by lia; replace (F + 432 + 8) with (F + 8 * 55) by lia; rewrite (D8 55) by lia; lia).
split; [|split; [|split]].
+ unfold m_have, SlotModel.rec_have. cbn [SlotModel.rec_hw].
apply val_mem_zero_of_aview. intros k Hk. unfold V_hw. rewrite <- (HZ (Z.of_nat k)) by lia. f_equal.
+ unfold bytes_at8, m_hwb, SlotModel.rec_hwb. cbn [SlotModel.rec_hw]. intros j Hj.
cbn [length repeat map] in Hj.
replace (nth j (map (fun b : byte => bv_unsigned b) (repeat (RcIdentModel.zb 0) 8)) 0) with 0.
2: { do 8 (destruct j as [|j]; [reflexivity|]). lia. }
split; [|lia].
apply val_mem_zero_of_aview. intros k Hk. assert (k = 0%nat) by lia. subst k.
unfold V_hw. rewrite <- (HZ (4 + Z.of_nat j)) by lia. f_equal. unfold V_hw. lia.
+ unfold sh_zero, zero_shadow. intros i Hi. change (N_hw / 8) with 1 in Hi. assert (i = 0) by lia. subst i.
unfold V_hw. fold F. replace (F + 432) with (F + 8 * 54) by lia. rewrite SHI by lia. exact HSH0.
+ unfold sh_blk, block_shadow. unfold V_hw, N_hw. fold F. replace (F + 432) with (F + 8 * 54) by lia.
split; [rewrite DF; replace (32 * (F / 32) + 8 * 54) with ((4 * (F / 32) + 54) * 8) by lia; apply Z_mod_mult|].
split; [lia|]. intros i Hi. change ((12 + 7) / 8) with 2 in Hi. rewrite SHI by lia.
assert (Hi2 : i = 0 \/ i = 1) by lia. destruct Hi2 as [-> | ->]; [exact HSH0 | exact HSH4].
Qed.

Definition Cend (g : ectx) (pos mf : Z) : world SEGS -> config -> Prop :=
fun W3 c3 => INV_REC g pos mf 0 W3 c3 \/ (m_nrec g = 0%nat /\ INV_EXIT g pos mf W3 c3).

Lemma C_close_rec : forall g pos mf ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4,
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly2 S2 W2 mem2 md2 0 ->
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly2 S2 W2 mem4 md4 0 ->
frames S2 = [(4, pos)] ->
mo_le MT (e_S g) S2 (0 * (mo_malloc MT 256 + mo_free MT)) ->
mo_ok MT S2 ((EV_LLVMF - 0) * (mo_malloc MT 256 + mo_free MT)) ->
HBLOCKS g ly2 S2 [] -> ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 -> id_at g pos 0 W2 mem2 ->
aview SEGS (w_H W2) mem2 (shadow_addr (SFa g pos + V_hw)) = Some 0 ->
aview SEGS (w_H W2) mem2 (shadow_addr (SFa g pos + V_hw + 8)) = Some 4 ->
(forall r : bv 5, In r [2; 3; 4; 8; 9; 19]%bv -> getr regs4 r = getr regs2 r) ->
(forall i, 0 <= i < 12 -> aview SEGS (w_H W2) mem4 (SFa g pos + V_hw + i) = Some 0) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ cwin (SFa g pos) mf a -> aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W2) mem2 a) ->
val_mem SEGS (rd W2 mem4) (mf + 80) 8 (SFa g pos) ->
getr regs4 20 = w64 0 -> getr regs4 21 = w64 6 -> getr regs4 24 = w64 (SFa g pos + V_before) ->
getr regs4 26 = w64 (e_p g + 1) -> getr regs4 18 = w64 (e_n g - 1) ->
(0 < m_nrec g)%nat -> 0 < e_n g ->
val_mem SEGS (rd W2 mem4) (mf + 112) 8 (SlotModel.nrec (e_pl g)) ->
mf_fixed g pos mf W2 mem4 -> mf_id g pos mf W2 mem4 -> mf_again g pos mf W2 mem4 ->
Cend g pos mf W2 (cfg_at SEGS (BASE + 0x414) regs4 mem4 md4).
Proof.
intros g pos mf ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4 HJ2 HJ4 HFR HMO HMOK HBL HEC HID HSH0 HSH4 HR HZ KEEP M80
R20 R21 R24 R26 R18 Hnr Hnp M112 MFX MID MAG.
destruct (C_keep g pos mf ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4 HJ2 HJ4 HFR HBL HEC HID HSH0 HSH4 HR HZ KEEP M80)
as (HEC4 & HID4 & HHW4).
pose proof HEC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
& _ & HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & HLEN & _).
assert (HC0 : m_cur g 0 = 1).
{ unfold m_cur, SlotModel.rec_c, SlotModel.nlen. rewrite <- HLEN. lia. }
left. exists ly2, S2, regs4, mem4, md4.
split; [reflexivity|]. split; [exact HJ4|]. split; [exact HFR|]. split; [unfold EV_LLVMF; lia|].
split; [exact HMO|]. split; [exact HMOK|]. split; [exact HEC4|].
split; [exact Hnr|]. split; [exact R20|]. split; [exact R21|]. split; [exact R24|].
split; [exact M112|]. split; [exact MFX|].
split; [unfold cur_at; rewrite HC0; split; [exact R26|]; split; [exact R18|]; lia|].
split; [exact HID4|]. split; [exact HHW4|]. split; [exact HBL|]. split; [exact MID|]. exact MAG.
Qed.

Lemma C_close_exit : forall g pos mf ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4,
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly2 S2 W2 mem2 md2 0 ->
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly2 S2 W2 mem4 md4 0 ->
frames S2 = [(4, pos)] ->
mo_le MT (e_S g) S2 (0 * (mo_malloc MT 256 + mo_free MT)) ->
mo_ok MT S2 ((EV_LLVMF - 0) * (mo_malloc MT 256 + mo_free MT)) ->
HBLOCKS g ly2 S2 [] -> ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 -> id_at g pos 0 W2 mem2 ->
aview SEGS (w_H W2) mem2 (shadow_addr (SFa g pos + V_hw)) = Some 0 ->
aview SEGS (w_H W2) mem2 (shadow_addr (SFa g pos + V_hw + 8)) = Some 4 ->
(forall r : bv 5, In r [2; 3; 4; 8; 9; 19]%bv -> getr regs4 r = getr regs2 r) ->
(forall i, 0 <= i < 12 -> aview SEGS (w_H W2) mem4 (SFa g pos + V_hw + i) = Some 0) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ cwin (SFa g pos) mf a -> aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W2) mem2 a) ->
val_mem SEGS (rd W2 mem4) (mf + 80) 8 (SFa g pos) ->
m_nrec g = 0%nat -> cur_at g 0 regs4 ->
val_mem SEGS (rd W2 mem4) (mf + 48) 8 (SFa g pos + V_hw) ->
val_mem SEGS (rd W2 mem4) (mf + 128) 8 (SFa g pos + V_id + 3) ->
mf_id g pos mf W2 mem4 ->
Cend g pos mf W2 (cfg_at SEGS (BASE + 0xe70) regs4 mem4 md4).
Proof.
intros g pos mf ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4 HJ2 HJ4 HFR HMO HMOK HBL HEC HID HSH0 HSH4 HR HZ KEEP M80
Hnr HCUR M48 M128 MID.
destruct (C_keep g pos mf ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4 HJ2 HJ4 HFR HBL HEC HID HSH0 HSH4 HR HZ KEEP M80)
as (HEC4 & HID4 & HHW4).
right. split; [exact Hnr|]. unfold inv_exit. rewrite Hnr.
exists ly2, S2, regs4, mem4, md4.
split; [reflexivity|]. split; [exact HJ4|]. split; [exact HFR|]. split; [unfold EV_LLVMF; lia|].
split; [exact HMO|]. split; [exact HMOK|]. split; [exact HEC4|].
split; [exact HCUR|]. split; [exact HID4|]. split; [exact HHW4|]. split; [exact HBL|].
split; [exact M48|]. split; [exact M128|]. exact MID.
Qed.

(* ---- the walk -------------------------------------------------------------------------------------------- *)
Lemma kept_fr : forall E rs H (m m' : word -> option byte) mf a,
c_wins_ok rs = true -> bv_unsigned (ew E 9) = mf -> frame_of E rs (mrestrict H m) (mrestrict H m') ->
0 <= a < 2 ^ 64 -> ~ (mf + 32 <= a < mf + 176) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' mf a Hok H9 HF Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
intros Hw. apply Hn. exact (c_nwr E rs a mf Hok H9 Hw).
Qed.

(* The value of the machine-frame slot at offset od in the run's state HS (a chunk of mf_region). *)
Ltac c_slot HS U9 od e H :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss (restrict ?Hh ?msx) =>
let rs := eval vm_compute in (ss_mem ss) in
lazymatch rs with (YP09.mkRegion (Some 9%nat) ?lo ?hi ?wlo ?whi ?cs) :: _ =>
let R := fresh "R" in
pose proof (st_ok_pi_region_nth Ex ss (restrict Hh msx) 0 (YP09.mkRegion (Some 9%nat) lo hi wlo whi cs) HS
ltac:(vm_compute; reflexivity)) as R;
pose proof (field_of_region_any Ex _ 9 _ cs lo hi wlo whi od 8 e R U9
ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as H;
clear R; cbn [ms_mem restrict] in H; change (N.to_nat 8) with 8%nat in H
end end.
(* The run writes only mf_region's window, which the window case of awr_byte allows. *)
Ltac c_awr U9 Hwin Hmf2 :=
let a := fresh "a" in let Ha := fresh "Ha" in let Hw := fresh "Hw" in
intros a Ha; left;
lazymatch type of Ha with in_wrange ?Ex ?rs a =>
pose proof (c_nwr Ex rs a _ ltac:(vm_compute; reflexivity) U9 Ha) as Hw end;
unfold ESTACK in Hwin; clear - Hw Hwin Hmf2; lia.
(* After a run: the memory outside mf_region's window is the one before the run. *)
Ltac c_keep U9 KR :=
lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict ?Hh ?m0) (mrestrict ?Hh ?m1) |- _ =>
lazymatch type of KR with forall a, _ -> _ -> aview _ _ m0 a = aview _ _ ?mb a =>
let KR' := fresh "KR" in
assert (KR' : forall a, 0 <= a < 2 ^ 64 -> ~ (_ + 32 <= a < _ + 176) -> aview SEGS Hh m1 a = aview SEGS Hh mb a)
by (let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in intros a Ha Hn;
rewrite (kept_fr Ex rs Hh m0 m1 _ a ltac:(vm_compute; reflexivity) U9 HFr Ha Hn); exact (KR a Ha Hn));
clear KR; rename KR' into KR
end end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

Theorem seg_C_meas : forall g pos mf W2 c2, INV_B g pos mf W2 c2 -> SRr SEGS W2 c2 (Cend g pos mf).
Proof.
intros g pos mf W2 c2 HB.
destruct HB as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HFR & HK & HMO & HMOK & HEC & HP).
destruct HP as (HID & HBL & M184 & M48 & R10 & R11 & R12 & R18 & R26 & HSH0 & HSH4).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
eapply SRr_bind; [exact (C_memset g pos mf ly2 S2 W2 regs2 mem2 md2 HJ HFR HEC R10 R11 R12 HSH0 HSH4) |].
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HR3 & HZ3 & HK3).
pose proof HEC as (R2 & R9 & R8 & HMF & HMF32 & R3 & R4 & R19 & M80 & M192 & M176 & _ & _ & _ & _ & _ & _ & _ & _
& _ & _ & _ & _ & _ & _ & _ & HPRE & _ & _ & HBY).
pose proof HPRE as (_ & _ & _ & _ & HINP & HLEN & _ & _ & _ & _ & HROS & _).
destruct (C_layout g pos mf ly2 S2 W2 mem2 md2 HJ HFR HMF) as (HFal & HF4096 & HFceil & HFapp & Hmf1 & Hmf2 & Hsp47 & C1 & Hwin & HFeq).
set (F := SFa g pos) in *.
assert (K3 : forall a v, mf <= a -> a + 8 <= mf + 320 -> val_mem SEGS (rd W2 mem2) a 8 v -> val_mem SEGS (rd W2 mem3) a 8 v).
{ intros a v Ha1 Ha2 Hv. apply (val_mem_keep _ mem2 mem3); [|exact Hv]. intros k Hk.
apply HK3; [clear - Ha1 Ha2 Hk Hmf1 Hmf2 Hsp47 C1; lia | unfold V_hw; clear - Ha1 Hk Hmf1 HFceil; lia | unfold ESTACK; clear - Ha1 Hk; lia]. }
assert (R2' : getr regs3 2 = w64 mf) by (rewrite (HR3 2%bv ltac:(cbn; tauto)); exact R2).
assert (R9' : getr regs3 9 = w64 mf) by (rewrite (HR3 9%bv ltac:(cbn; tauto)); exact R9).
assert (R18' : getr regs3 18 = w64 (e_n g)) by (rewrite (HR3 18%bv ltac:(cbn; tauto)); exact R18).
assert (R26' : getr regs3 26 = w64 (e_p g)) by (rewrite (HR3 26%bv ltac:(cbn; tauto)); exact R26).
assert (HR4 : forall regs4 : bvmap 5 word, (forall r : bv 5, In r [2; 3; 4; 8; 9; 19]%bv -> getr regs4 r = getr regs3 r) ->
forall r : bv 5, In r [2; 3; 4; 8; 9; 19]%bv -> getr regs4 r = getr regs2 r).
{ intros regs4 H r Hr. rewrite (H r Hr). apply HR3. cbn [In] in Hr |- *. tauto. }
assert (HZ4 : forall m4 : word -> option byte, (forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 32 <= a < mf + 176) ->
aview SEGS (w_H W2) m4 a = aview SEGS (w_H W2) mem3 a) ->
forall i, 0 <= i < 12 -> aview SEGS (w_H W2) m4 (F + V_hw + i) = Some 0).
{ intros m4 H i Hi. rewrite H; [exact (HZ3 i Hi)| clear - Hi HF4096 HFceil Hmf1 Hmf2 Hsp47 C1; unfold V_hw; lia |].
unfold V_hw. clear - Hi HFceil Hmf1. lia. }
assert (HK4 : forall m4 : word -> option byte, (forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 32 <= a < mf + 176) ->
aview SEGS (w_H W2) m4 a = aview SEGS (w_H W2) mem3 a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ cwin F mf a -> aview SEGS (w_H W2) m4 a = aview SEGS (w_H W2) mem2 a).
{ intros m4 H a Ha Hc. unfold cwin in Hc. rewrite H by tauto.
apply HK3; [exact Ha | intros Hh; apply Hc; left; unfold V_hw in Hh; lia | intros Hh; apply Hc; right; left; exact Hh]. }
destruct HINP as [(Hn0 & Hp0) | (Hnp & Hinb)].
- (* the empty input: 0x80a8c jumps to the exit *)
pose proof (C_entry_zero g pos mf ly2 S2 W2 mem3 md3 regs3 HJ3 HFR R2' R9' HMF HMF32
(K3 (mf + 48) _ ltac:(lia) ltac:(lia) M48) (K3 (mf + 80) _ ltac:(lia) ltac:(lia) M80)
(K3 (mf + 176) _ ltac:(lia) ltac:(lia) M176) (K3 (mf + 184) _ ltac:(lia) ltac:(lia) M184)) as HS0.
pose proof (st_ok_pi_pin_reg' _ _ _ (18%bv : bv 5) 0 HS0 ltac:(cbn [ms_regs restrict mkst]; rewrite R18', Hn0; reflexivity) eq_refl) as HS.
clear HS0. lazymatch type of HS with st_ok_pi _ _ _ ?ss1 _ => let ss2 := eval vm_compute in ss1 in change ss1 with ss2 in HS end.
fold F in HS. remember (EZ regs3 F) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite (EE 9%nat 9%bv eq_refl), R9'. unfold w64. apply unsigned_lit_small. clear - Hmf1 Hmf2 Hsp47 C1. lia. }
assert (E33 : ew E 33 = Z_to_bv 64 F) by (subst E; unfold EZ; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
assert (HAE : env_agree 32 (Ereg regs3 (map (Z_to_bv 64) [SB_C; F])) E)
by (split; [intros n Hn; subst E; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
assert (SHOK : sh_ok SEGS Bx_C [] E (mrestrict (w_H W2) mem3)) by constructor.
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 32 <= a < mf + 176) -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem3 a)
by (intros; reflexivity).
assert (E26 : ew E 26 = w64 (e_p g)) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26').
clear HE EE.
unfold cfg_at. change (w64 (BASE + 0x374)) with (Z_to_bv 64 (BASE + 0x374)).
paj_run_to_tok RUNTO HS HJ3 SHOK Bspan_C 0xe70; [c_awr U9 Hwin Hmf2 |].
c_keep U9 KR.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs3 _ [2; 3; 4; 8; 9; 19]%bv HS HAE ltac:(vm_compute; reflexivity)) as HKR.
cbn [ms_regs restrict] in HKR.
prreg HS (26%bv : bv 5) Q26. prreg HS (18%bv : bv 5) Q18.
assert (RF : 0 <= F /\ F + 1024 < 2 ^ 64) by (clear - HF4096 HFceil Hmf1 Hmf2 Hsp47 C1; lia).
c_slot HS U9 48 (SOff 33 432) V48. c_slot HS U9 80 (SOff 33 0) V80.
c_slot HS U9 128 (SOff 33 355) V128. c_slot HS U9 184 (SOff 33 352) V184.
rewrite (soff_mod E 33 F 432 E33 ltac:(lia) ltac:(lia)) in V48.
rewrite (soff_mod E 33 F 0 E33 ltac:(lia) ltac:(lia)), Z.add_0_r in V80.
rewrite (soff_mod E 33 F 355 E33 ltac:(lia) ltac:(lia)) in V128.
rewrite (soff_mod E 33 F 352 E33 ltac:(lia) ltac:(lia)) in V184.
assert (Hpl : e_pl g = []) by (destruct (e_pl g); [reflexivity | cbn in HLEN; lia]).
assert (Hnr0 : m_nrec g = 0%nat) by (unfold m_nrec, SlotModel.nrecn, SlotModel.nrec, SlotModel.inb; rewrite Hpl; reflexivity).
pmkst HS. apply SRr_ret.
apply (C_close_exit g pos mf ly2 S2 W2 regs2 mem2 md2 _ _ _ HJ HJ3 HFR HMO HMOK HBL HEC HID HSH0 HSH4 (HR4 _ HKR) (HZ4 _ KR) (HK4 _ KR) V80 Hnr0).
+ unfold cur_at, m_cur, SlotModel.rec_c, SlotModel.nlen. rewrite Hpl. cbn [length Z.of_nat Z.min].
rewrite Q26, E26, Q18, Hn0, Hp0. rewrite !Z.add_0_r. split; [reflexivity|]. split; [reflexivity | lia].
+ exact V48.
+ replace (F + 355) with (F + V_id + 3) in V128 by (unfold V_id; lia). exact V128.
+ exact V184.
- (* a non-empty input *)
assert (Hin : In (e_p g, e_n g) (ablocks B ly2 S2))
by (destruct HBL as [HP _]; apply (Permutation_in _ (Permutation_sym HP)); exact Hinb).
pose proof HJ as (HAR2 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hin) as (Hp16 & Hp4096 & Hpceil & Happ & _).
pose proof (req_size_pos0 (e_n g) ltac:(lia)) as Hreq.
assert (Hfin : In (4, pos) (frames S2)) by (rewrite HFR; left; reflexivity).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ 4 pos HAR2 Hin Hfin) as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite HFeq in Hsep. change (fs_frame_bytes 4) with 1024 in Hsep.
assert (MX0 : val_mem SEGS (rd W2 mem3) (e_p g) 1 (SlotModel.inb (e_pl g) 0)).
{ unfold bytes_at8 in HBY. destruct (e_pl g) as [|b0 rest] eqn:Epl; [cbn in HLEN; lia|].
destruct (HBY 0%nat ltac:(cbn; lia)) as [Hv _]. cbn [nth map] in Hv. rewrite Z.add_0_r in Hv.
unfold SlotModel.inb, RcIdentModel.bz, RcIdentModel.nthb. cbn [nth Z.to_nat].
apply (val_mem_keep _ mem2 mem3); [|exact Hv]. intros k Hk. assert (k = 0%nat) by lia. subst k. rewrite Z.add_0_r.
apply HK3; [clear - Hp4096 Hpceil Hreq Hmf1 Hmf2 Hsp47 C1; lia | unfold V_hw; clear - Hsep Hreq; lia
| unfold ESTACK; clear - Hpceil Hreq Hmf1; lia]. }
assert (MC5 : val_mem SEGS (rd W2 mem3) (VAL (A_OBJ 5)) 8 C5).
{ refine (proj1 (HIMG W2 mem3 _)).
apply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3).
apply HRO. exact HROS. }
pose proof (C_entry_pos g pos mf ly2 S2 W2 mem3 md3 regs3 HJ3 HFR R2' R9' R18' R26' HMF HMF32 Hnp Hin
(K3 (mf + 48) _ ltac:(lia) ltac:(lia) M48) (K3 (mf + 80) _ ltac:(lia) ltac:(lia) M80)
(K3 (mf + 176) _ ltac:(lia) ltac:(lia) M176) (K3 (mf + 184) _ ltac:(lia) ltac:(lia) M184) MX0 MC5) as HS.
set (x0 := SlotModel.inb (e_pl g) 0) in *.
set (s0 := if 0 <? e_n g / 8 then 0 else e_n g mod 8) in *.
assert (Rx0 : 0 <= x0 < 256) by (subst x0; unfold SlotModel.inb, RcIdentModel.bz; apply (bv_unsigned_in_range 8)).
assert (Rs0 : 0 <= s0 <= 7) by (subst s0; destruct (0 <? e_n g / 8); [lia | pose proof (Z.mod_pos_bound (e_n g) 8 ltac:(lia)); lia]).
fold F in HS. remember (EC regs3 F x0 s0 (e_p g)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (map (Z_to_bv 64) [SB_C; F; x0; s0; SB_C + e_p g / 8]) (Z_to_bv 64 0))
by (intros j Hj; subst E; unfold EC; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite (EE 9%nat 9%bv eq_refl), R9'. unfold w64. apply unsigned_lit_small. clear - Hmf1 Hmf2 Hsp47 C1. lia. }
pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
cbn [nth map Nat.add] in E33, E34, E35.
assert (E26 : ew E 26 = w64 (e_p g)) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26').
assert (E18 : ew E 18 = w64 (e_n g)) by (rewrite (EE 18%nat 18%bv eq_refl); exact R18').
assert (HAE : env_agree 32 (Ereg regs3 (map (Z_to_bv 64) [SB_C; F; x0; s0; SB_C + e_p g / 8])) E)
by (split; [intros n Hn; subst E; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
assert (SHOK : sh_ok SEGS Bx_C [] E (mrestrict (w_H W2) mem3)) by constructor.
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 32 <= a < mf + 176) -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem3 a)
by (intros; reflexivity).
assert (RF : 0 <= F /\ F + 1024 < 2 ^ 64) by (clear - HF4096 HFceil Hmf1 Hmf2 Hsp47 C1; lia).
assert (Rp : 4096 <= e_p g /\ e_p g + 1 < 2 ^ 64) by (clear - Hp4096 Hpceil Hreq Hmf1 Hmf2 Hsp47 C1; lia).
assert (Rn : 0 < e_n g < 2 ^ 26) by exact Hnp.
clear HE EE EX.
unfold cfg_at. change (w64 (BASE + 0x374)) with (Z_to_bv 64 (BASE + 0x374)).
(* the closing steps, on whichever path reaches them *)
let nrec_of b :=
lazymatch goal with Hb : branch_taken BC_EQ (sv_denot _ (SAlu ALU_SUB _ _)) _ = b |- _ =>
pose proof (nrec_br E x0 E34 Rx0) as Hnb; unfold NREC_SV, C5 in Hnb; rewrite Hnb in Hb; clear Hnb end in
let regs_end := idtac;
lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ =>
pose proof (regs_kept_of_st_ok_pi _ _ _ regs3 _ [2; 3; 4; 8; 9; 19]%bv HS HAE ltac:(vm_compute; reflexivity)) as HKR;
cbn [ms_regs restrict] in HKR;
prreg HS (26%bv : bv 5) Q26; prreg HS (18%bv : bv 5) Q18;
rewrite E26 in Q26; rewrite E18 in Q18; unfold w64 in Q26, Q18;
rewrite unsigned_lit_small in Q26, Q18 by lia;
replace (e_n g + -1) with (e_n g - 1) in Q18 by lia end in
let close_exit := idtac;
paj_run_to_tok RUNTO HS HJ3 SHOK Bspan_C 0xe70; [c_awr U9 Hwin Hmf2 |];
c_keep U9 KR; nrec_of true; regs_end;
c_slot HS U9 48 (SOff 33 432) V48; c_slot HS U9 80 (SOff 33 0) V80;
c_slot HS U9 128 (SOff 33 355) V128; c_slot HS U9 184 (SOff 33 352) V184;
rewrite (soff_mod E 33 F 432 E33 ltac:(lia) ltac:(lia)) in V48;
rewrite (soff_mod E 33 F 0 E33 ltac:(lia) ltac:(lia)), Z.add_0_r in V80;
rewrite (soff_mod E 33 F 355 E33 ltac:(lia) ltac:(lia)) in V128;
rewrite (soff_mod E 33 F 352 E33 ltac:(lia) ltac:(lia)) in V184;
lazymatch goal with Hb : (x0 mod 65 =? 0) = true |- _ =>
apply Z.eqb_eq in Hb;
assert (Hnr0 : m_nrec g = 0%nat) by (unfold m_nrec, SlotModel.nrecn, SlotModel.nrec; fold x0; rewrite Hb; reflexivity) end;
assert (HC0 : m_cur g 0 = 1) by (unfold m_cur, SlotModel.rec_c, SlotModel.nlen; rewrite <- HLEN; lia);
lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ => pmkst HS end; apply SRr_ret;
apply (C_close_exit g pos mf ly2 S2 W2 regs2 mem2 md2 _ _ _ HJ HJ3 HFR HMO HMOK HBL HEC HID HSH0 HSH4 (HR4 _ HKR) (HZ4 _ KR) (HK4 _ KR) V80 Hnr0);
[ unfold cur_at; rewrite HC0; split; [exact Q26 |]; split; [exact Q18 | lia]
| exact V48
| replace (F + 355) with (F + V_id + 3) in V128 by (unfold V_id; lia); exact V128
| exact V184 ] in
let close_rec := idtac;
paj_run_to_tok RUNTO HS HJ3 SHOK Bspan_C 0x414; [c_awr U9 Hwin Hmf2 |];
c_keep U9 KR; nrec_of false; regs_end;
prreg HS (20%bv : bv 5) Q20; prreg HS (21%bv : bv 5) Q21; prreg HS (24%bv : bv 5) Q24;
rewrite E33 in Q24; rewrite unsigned_lit_small in Q24 by lia;
c_slot HS U9 32 (SOff 33 224) V32; c_slot HS U9 40 (SOff 33 192) V40;
c_slot HS U9 48 (SOff 33 432) V48; c_slot HS U9 72 (SOff 33 288) V72;
c_slot HS U9 80 (SOff 33 0) V80; c_slot HS U9 88 (SOff 33 32) V88;
c_slot HS U9 96 (SOff 33 140) V96; c_slot HS U9 104 (SOff 33 115) V104;
c_slot HS U9 112 NREC_SV V112; c_slot HS U9 120 (SOff 33 380) V120;
c_slot HS U9 128 (SOff 33 355) V128; c_slot HS U9 168 (SOff 33 112) V168;
c_slot HS U9 184 (SOff 33 352) V184;
rewrite (soff_mod E 33 F 224 E33 ltac:(lia) ltac:(lia)) in V32;
rewrite (soff_mod E 33 F 192 E33 ltac:(lia) ltac:(lia)) in V40;
rewrite (soff_mod E 33 F 432 E33 ltac:(lia) ltac:(lia)) in V48;
rewrite (soff_mod E 33 F 288 E33 ltac:(lia) ltac:(lia)) in V72;
rewrite (soff_mod E 33 F 0 E33 ltac:(lia) ltac:(lia)), Z.add_0_r in V80;
rewrite (soff_mod E 33 F 32 E33 ltac:(lia) ltac:(lia)) in V88;
rewrite (soff_mod E 33 F 140 E33 ltac:(lia) ltac:(lia)) in V96;
rewrite (soff_mod E 33 F 115 E33 ltac:(lia) ltac:(lia)) in V104;
rewrite (soff_mod E 33 F 380 E33 ltac:(lia) ltac:(lia)) in V120;
rewrite (soff_mod E 33 F 355 E33 ltac:(lia) ltac:(lia)) in V128;
rewrite (soff_mod E 33 F 112 E33 ltac:(lia) ltac:(lia)) in V168;
rewrite (soff_mod E 33 F 352 E33 ltac:(lia) ltac:(lia)) in V184;
rewrite (nrec_denot E x0 E34 Rx0) in V112;
rewrite unsigned_lit_small in V112 by (pose proof (Z.mod_pos_bound x0 65 ltac:(lia)); lia);
rewrite (Z.mod_small (x0 mod 65)) in V112 by (pose proof (Z.mod_pos_bound x0 65 ltac:(lia)); change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia);
lazymatch goal with Hb : (x0 mod 65 =? 0) = false |- _ =>
apply Z.eqb_neq in Hb;
assert (Hnr : (0 < m_nrec g)%nat)
by (unfold m_nrec, SlotModel.nrecn, SlotModel.nrec; fold x0; pose proof (Z.mod_pos_bound x0 65 ltac:(lia)); lia) end;
lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ => pmkst HS end; apply SRr_ret;
apply (C_close_rec g pos mf ly2 S2 W2 regs2 mem2 md2 _ _ _ HJ HJ3 HFR HMO HMOK HBL HEC HID HSH0 HSH4 (HR4 _ HKR) (HZ4 _ KR) (HK4 _ KR) V80
Q20 Q21 Q24 Q26 Q18 Hnr ltac:(lia) V112);
[ unfold mf_fixed; split; [exact V32|]; split; [exact V40|]; split; [exact V48|]; split; [exact V72|];
split; [exact V88|];
split; [replace (F + 140) with (F + V_again + 28) in V96 by (unfold V_again; lia); exact V96|];
split; [replace (F + 115) with (F + V_again + 3) in V104 by (unfold V_again; lia); exact V104|];
split; [replace (F + 380) with (F + V_id + 28) in V120 by (unfold V_id; lia); exact V120|];
replace (F + 355) with (F + V_id + 3) in V128 by (unfold V_id; lia); exact V128
| exact V184
| exact V168 ] in
let nrec_branch :=
psrr_branch_tok RUN BR HS SHOK Bspan_C; [ close_exit | close_rec ] in
paj_run_tok RUN HS HJ3 SHOK Bspan_C; [c_awr U9 Hwin Hmf2 |];
c_keep U9 KR;
psrr_branch_tok RUN BR HS SHOK Bspan_C;
[ (* the shadow cell is 0: the byte is addressable at once *)
paj_run_tok RUN HS HJ3 SHOK Bspan_C; [c_awr U9 Hwin Hmf2 |]; c_keep U9 KR; nrec_branch
| (* a partial granule: the slow path 0x82310 compares p & 7 with the cell *)
paj_run_tok RUN HS HJ3 SHOK Bspan_C; [c_awr U9 Hwin Hmf2 |]; c_keep U9 KR;
psrr_branch_tok RUN BR HS SHOK Bspan_C;
[ exfalso;
lazymatch goal with H1 : branch_taken BC_EQ (sv_denot _ (SOff 35 0)) _ = false,
H2 : branch_taken BC_GE _ (sv_denot _ (SOff 35 0)) = true |- _ =>
exact (s0_dead E s0 E35 Rs0 H1 H2) end
| paj_run_tok RUN HS HJ3 SHOK Bspan_C; [c_awr U9 Hwin Hmf2 |]; c_keep U9 KR; nrec_branch ] ].
Qed.

Theorem seg_C_holds : SEG_C.
Proof. exact seg_C_meas. Qed.

End c.
End b.
End a.
