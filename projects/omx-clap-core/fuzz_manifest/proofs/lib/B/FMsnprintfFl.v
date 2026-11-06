(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMsnprintfFl.v at a working branch 5d8d8a15571, relocated A->B by Theorem Labs tools over the unstripped twins; every image numeral re-derived by symbol / section (a Theorem Labs lane reloc report). *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new contract of musl sn_write as vfprintf's flush f->write (f, 0, 0) on musl
   vsnprintf's FILE at fm.asan addresses, by FMsnprintfFw.v's sink-call kit (A/YE3h.v's VI_run / vf_phase adapted). *)
(* vfprintf's flush f->write (f, 0, 0) = sn_write on the snprintf FILE: the buffered bytes (when any) and a NUL reach
   the destination behind the cookie, wpos = wbase = buf, a0 = 0. Stated over the sink invariant SNK (FMsnprintfI.v). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YE34 YF0l YE3e YE3f YE3g YE6g YE39 YE2p YE3i YE3h YF0m YE22 YF0x YE20 YE2y YE7f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Base FMsnprintfI FMsnprintfK FMsnprintfFw0 FMsnprintfFw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
(* The symbolic entry state of sn_write (fm 0x922c0) for vfprintf's flush f->write (f, 0, 0): frame base (atom 2)
   = sp0, musl vfprintf's entry sp; sn_write entered with sp = sp0 + OSP_PC, a0 = f = sp0 + FO, a1 = a2 = 0.
   Extra atoms as in fw0: 33 = b (bytes in the internal buffer), 34 = the cookie's s, 35 = the cookie's n. *)
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition fl_regions : smem :=
[ YP09.mkRegion (Some 2%nat) (- SNK_STK) 0 (- SNK_STK) OSP_PC [];
  YP09.mkRegion (Some 2%nat) FO (FO + 0xe8) (FO + 40) (FO + 64) fw_chunks;
  YP09.mkRegion (Some 2%nat) CKO (CKO + 16) CKO (CKO + 16)
    [YP09.mkChunk CKO (CVal 8 (SOff 34 0)); YP09.mkChunk (CKO + 8) (CVal 8 (SOff 35 0))] ].
Definition fl_sr : list sv :=
sr_set (sr_set (sr_set (sr_set sr_atoms (2%bv : bv 5) (SOff 2 OSP_PC)) (10%bv : bv 5) (SOff 2 FO)) (11%bv : bv 5) (SLit 0))
  (12%bv : bv 5) (SLit 0).
Definition fl_facts : facts := mkFacts [ (2%nat, mkAF (2 ^ 44) (2 ^ 47) 4); (33%nat, mkAF 0 80 0);
  (34%nat, mkAF 1 (2 ^ 47) 0); (35%nat, mkAF 0 (2 ^ 31) 0) ] [] [].
Definition fl0 : sstate := mkSS A_SNW fl_sr fl_regions None fl_facts.
Definition f1_s : sstate := Eval vm_compute in (fl0).
Definition f1_e : sstate := Eval vm_compute in fst (RUN f1_s).
Lemma r_f1 : RUN f1_s = (f1_e, RS_stopped (SR_branch BC_LTU (SOff 35 0) (SOff 33 0))). Proof. vm_compute. reflexivity. Qed.
Definition f2_s : sstate := Eval vm_compute in (AC f1_e BC_GEU (SOff 35 0) (SOff 33 0)).
Definition f2_e : sstate := Eval vm_compute in fst (RUN f2_s).
Lemma r_f2 : RUN f2_s = (f2_e, RS_stopped (SR_branch BC_EQ (SOff 33 0) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition fZ1_s : sstate := Eval vm_compute in (AC f2_e BC_EQ (SOff 33 0) (SLit 0)).
Definition fZ1_e : sstate := Eval vm_compute in fst (RUN fZ1_s).
Lemma r_fZ1 : RUN fZ1_s = (fZ1_e, RS_stopped (SR_store (Some 34%nat) 0)). Proof. vm_compute. reflexivity. Qed.
Definition fZ2_s : sstate := Eval vm_compute in (set_regs_pc fZ1_e [] 0x92368).
Definition fZ2_e : sstate := Eval vm_compute in fst (RUN fZ2_s).
Lemma r_fZ2 : RUN fZ2_s = (fZ2_e, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.
Definition fN1_s : sstate := Eval vm_compute in (AC f2_e BC_NE (SOff 33 0) (SLit 0)).
Definition fN1_e : sstate := Eval vm_compute in fst (RUN fN1_s).
Lemma r_fN1 : RUN fN1_s = (fN1_e, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition fN2_s : sstate := Eval vm_compute in (kafter 40 fN1_e 0x9231c (-432) 0 0).
Definition fN2_e : sstate := Eval vm_compute in fst (RUN fN2_s).
Lemma r_fN2 : RUN fN2_s = (fN2_e, RS_stopped (SR_branch BC_LTU (SAlu ALU_ADD (SMd M_MUL (SOff 33 0) (SLit (-1))) (SOff 35 0)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition fN3_s : sstate := Eval vm_compute in (AC fN2_e BC_GEU (SAlu ALU_ADD (SMd M_MUL (SOff 33 0) (SLit (-1))) (SOff 35 0)) (SLit 0)).
Definition fN3_e : sstate := Eval vm_compute in fst (RUN fN3_s).
Lemma r_fN3 : RUN fN3_s = (fN3_e, RS_stopped (SR_addr (SAlu ALU_ADD (SOff 33 0) (SOff 34 0)))). Proof. vm_compute. reflexivity. Qed.
Definition fN4_s : sstate := Eval vm_compute in (set_regs_pc fN3_e [] 0x92368).
Definition fN4_e : sstate := Eval vm_compute in fst (RUN fN4_s).
Lemma r_fN4 : RUN fN4_s = (fN4_e, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.
End r.
Lemma T_PC : OSP_FW <= OSP_PC <= OSP_PC.
Proof. unfold OSP_FW, OSP_PC. lia. Qed.
Section q. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Hypothesis AMEMCPY : aintrin_realizesU B OCpy W_MEMCPY.
Variables (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (sp0 D N M : Z) (out : list Z) (b : Z).
Let w := Z.of_nat (length out) - b.
(* snk_base *)
Hypothesis HAR : ARU tfibsegs B ly S U W mem md.
Hypothesis Hac : alloc_ceiling <= ly_stk_lo ly.
Hypothesis Hsp44 : 2 ^ 44 <= sp0.
Hypothesis Hsp16 : sp0 mod 16 = 0.
Hypothesis Hstk : ly_stk_lo ly + SNK_STK <= sp0.
Hypothesis Htop : sp0 + 0x200 <= ly_stk_hi ly.
Hypothesis Hsp47 : sp0 + 0x200 <= 2 ^ 47.
Hypothesis Hhigh : kHighMemBeg <= sp0 - SNK_STK.
Hypothesis Hpres : forall a, sp0 - SNK_STK <= a < sp0 + 0x200 -> apresent (w_H W) mem a.
Hypothesis Hzsh : zero_shadow (aview tfibsegs (w_H W) mem) SHADOW_OFF (sp0 - SNK_STK) (SNK_STK + 0x200).
(* snk_regs and the arguments *)
Hypothesis G1 : YK0s.ret_ok (getr regs 1).
Hypothesis G2 : getr regs 2 = w64 (sp0 + OSP_PC).
Hypothesis G3 : getr regs 3 = w64 (as_gp B).
Hypothesis G4 : getr regs 4 = w64 (as_tp B).
Hypothesis G10 : getr regs 10 = w64 (sp0 + FO).
Hypothesis G11 : getr regs 11 = w64 0.
Hypothesis G12 : getr regs 12 = w64 0.
Hypothesis HSNK : SNK W mem sp0 D N out b.
(* snk_dest D M *)
Hypothesis HD0 : 0 < D.
Hypothesis HDac : D + M <= alloc_ceiling.
Hypothesis HM : 1 <= M <= 2 ^ 30.
Hypothesis Hcan : D + M <= FM_canary \/ FM_canary + 8 <= D.
Hypothesis HDw : forall a, D <= a < D + M ->
writable_at tfibsegs (mrestrict (w_H W) mem) a /\ ~ aowned B ly S a /\ ~ in_rom tfibsegs a.
Hypothesis HDam : amem_range D M.
Hypothesis HDra : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF D M.
Hypothesis HDhu : shadow_hull_vis (aview tfibsegs (w_H W) mem) D M.
(* room *)
Hypothesis Hroom : Z.of_nat (length out) + 1 <= M <= N.
Hypothesis HN : N <= 2 ^ 30.
Definition fl_extra : list word := [Z_to_bv 64 0; Z_to_bv 64 b; Z_to_bv 64 (D + w); Z_to_bv 64 (N - 1 - w)].
Definition F0 : env := kenv regs sp0 fl_extra.
Lemma F0_reg : forall i (r : bv 5), i <> 2%nat -> Z.of_nat i = bv_unsigned r -> ew F0 i = getr regs r.
Proof. intros i r Hi Hr. apply kenv_reg; assumption. Qed.
Lemma F0_2 : bv_unsigned (ew F0 2) = sp0.
Proof. unfold F0. rewrite kenv_2. rewrite unsigned_lit_small; [reflexivity|]. lia. Qed.
Lemma F0_x : forall j, ew F0 (32 + j) = nth j fl_extra (Z_to_bv 64 0).
Proof. intros j. apply kenv_x. Qed.
Lemma fl_basic : 0 <= b <= 80 /\ 0 <= w /\ w + b <= N - 1 /\ 0 <= N.
Proof.
pose proof HSNK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hb & Hbo & Ho & _).
unfold w. lia.
Qed.
Lemma fl_regs_ok : regs_ok F0 fl_sr regs.
Proof.
pose proof F0_2 as E2.
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- getr _ ?r = sv_denot _ (sr_get ?sr ?r) =>
let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
cbn [sv_denot];
first [ reflexivity
| (rewrite Z.add_0_r;
match goal with |- getr _ ?r = Z_to_bv 64 (bv_unsigned (ew F0 ?i)) =>
rewrite (F0_reg i r) by (cbv; first [discriminate | reflexivity]) end;
rewrite Z_to_bv_bv_unsigned; reflexivity)
| (rewrite E2; first [rewrite G2 | rewrite G10]; reflexivity)
| (first [rewrite G11 | rewrite G12]; reflexivity) ] |]).
destruct Hr.
Qed.
Lemma fl_val_chunk : forall (e : sv) (off : Z) (n : BinNums.N) v,
sv_denot F0 e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 + off) (N.to_nat n) v ->
YP09.chunk_ok tfibsegs F0 (mrestrict (w_H W) mem) sp0 (YP09.mkChunk off (CVal n e)).
Proof.
intros e off n v He Hv Hn Hm.
exact (chunk_ok_val tfibsegs F0 _ sp0 off n e v He Hv Hn Hm).
Qed.
Lemma fl_entry_ok : st_ok tfibsegs F0 fl0 (restrict (w_H W) (mkst regs (Z_to_bv 64 A_SNW) mem (seg_rom tfibsegs))).
Proof.
pose proof F0_2 as E2. pose proof fl_basic as (Hb & Hw & Hsum & HN0). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HSNK as (S0 & S32 & S40 & S56 & S72 & S88 & S144 & S152 & SC0 & SC8 & SIB & SD & SDn & _ & _ & _ & _).
assert (HES : SNK_STK = 9104) by reflexivity.
assert (E33 : bv_unsigned (ew F0 33) = b) by (change (ew F0 33) with (ew F0 (32 + 1)); rewrite F0_x; cbn [nth fl_extra]; apply unsigned_lit_small; lia).
assert (E34 : ew F0 34 = Z_to_bv 64 (D + w)) by (change (ew F0 34) with (ew F0 (32 + 2)); rewrite F0_x; reflexivity).
assert (E35 : ew F0 35 = Z_to_bv 64 (N - 1 - w)) by (change (ew F0 35) with (ew F0 (32 + 3)); rewrite F0_x; reflexivity).
assert (E34' : bv_unsigned (ew F0 34) = D + w) by (rewrite E34; apply unsigned_lit_small; lia).
assert (E35' : bv_unsigned (ew F0 35) = N - 1 - w) by (rewrite E35; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold fl0.
apply kentry.
- exact fl_regs_ok.
- vm_compute. reflexivity.
- unfold fl_regions. repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply apresent_writable. apply Hpres. unfold OSP_PC in Ho. lia.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
cbn [base_val]. rewrite E2. unfold CKO, FO in *.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply apresent_writable. apply Hpres. lia. }
unfold fw_chunks. repeat apply Forall_cons; try apply Forall_nil;
(eapply fl_val_chunk; [ | | | first [eassumption | rewrite Z.add_assoc; eassumption]]);
first [ reflexivity | (unfold IBO, FO, CKO, A_SNW; zside)
| (cbn [sv_denot]; rewrite E2; f_equal; unfold IBO, CKO, FO; lia)
| (rewrite denot_lit_U, U_add_off_atom;
[ rewrite E2, E33; f_equal; lia | rewrite E2, E33; unfold M64, IBO; lia | rewrite E33; unfold M64; lia ]) ].
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
cbn [base_val]. rewrite E2. unfold CKO, FO in *.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply apresent_writable. apply Hpres. lia. }
repeat apply Forall_cons; try apply Forall_nil;
(eapply fl_val_chunk; [ | | | first [eassumption | rewrite Z.add_assoc; eassumption]]);
first [ (unfold IBO, FO, CKO, A_SNW; zside)
| (cbn [sv_denot]; rewrite Z.add_0_r; first [rewrite E34' | rewrite E35']; reflexivity) ].
- apply pairwise_disjoint_of_extents. unfold fl_regions, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2.
unfold CKO, FO. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I].
cbn [fl_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E33, E34', E35'. change (2 ^ 4) with 16. change (2 ^ 0) with 1.
repeat split; first [exact Hsp16 | apply Z.mod_1_r | lia].
Qed.
(* ---- the kit at OSP_PC ---- *)
Let HBp : snk_base B ly S U W mem md sp0 :=
conj HAR (conj Hac (conj Hsp44 (conj Hsp16 (conj Hstk (conj Htop (conj Hsp47 (conj Hhigh (conj Hpres Hzsh)))))))).
Let HDp : snk_dest B ly S W mem D M := conj HD0 (conj HDac (conj HM (conj Hcan (conj HDw (conj HDam (conj HDra HDhu)))))).
#[local] Abbreviation FWIq := (FWI B ly S U W mem md sp0 D M OSP_PC).
Let PH := fw_phase B ly S U W mem md sp0 D M OSP_PC LAWS AMEMCPY HBp HDp T_PC.
Let MC := fw_mcpy B ly S U W mem md sp0 D M OSP_PC LAWS AMEMCPY HBp HDp T_PC.
Let NUL := fw_nul B ly S U W mem md sp0 D M OSP_PC LAWS AMEMCPY HBp HDp T_PC.
Let RET := fw_ret B ly S U W mem md sp0 D M OSP_PC LAWS AMEMCPY HBp HDp T_PC.
Let SNKI := snk_intro B ly S U W mem md sp0 D M OSP_PC LAWS AMEMCPY HBp HDp T_PC.
Let FINIT := FWI_init B ly S U W mem md sp0 D M OSP_PC LAWS AMEMCPY HBp HDp T_PC.
Let FBAND := FWI_band B ly S U W mem md sp0 D M OSP_PC LAWS AMEMCPY HBp HDp T_PC.
Let FWR := FWI_writable B ly S U W mem md sp0 D M OSP_PC LAWS AMEMCPY HBp HDp T_PC.
Let BRA := band_ra B ly S U W mem md sp0 D M OSP_PC LAWS AMEMCPY HBp HDp T_PC.
Let BHU := band_hull B ly S U W mem md sp0 D M OSP_PC LAWS AMEMCPY HBp HDp T_PC.
Let BAM := band_amem B ly S U W mem md sp0 D M OSP_PC LAWS AMEMCPY HBp HDp T_PC.
Let DRA := dest_ra B ly S U W mem md sp0 D M OSP_PC LAWS AMEMCPY HBp HDp T_PC.
Let DHU := dest_hull B ly S U W mem md sp0 D M OSP_PC LAWS AMEMCPY HBp HDp T_PC.
Let DAM := dest_amem B ly S U W mem md sp0 D M OSP_PC LAWS AMEMCPY HBp HDp T_PC.
Definition F0like (E : env) : Prop := forall i, (i < 40)%nat -> ew E i = ew F0 i.
Lemma F0like_F0 : F0like F0.
Proof. intros i _. reflexivity. Qed.
Lemma F0like_havoc : forall E k ws, F0like E -> (40 <= k)%nat -> F0like (havoc E k ws).
Proof. intros E k ws HE Hk i Hi. rewrite ew_havoc_old by lia. apply HE, Hi. Qed.
Lemma F0like_at : forall E, F0like E ->
bv_unsigned (ew E 2) = sp0 /\ ew E 3 = w64 (as_gp B) /\ ew E 4 = w64 (as_tp B) /\
bv_unsigned (ew E 33) = b /\ bv_unsigned (ew E 34) = D + w /\ bv_unsigned (ew E 35) = N - 1 - w /\
(forall i (r : bv 5), i <> 2%nat -> Z.of_nat i = bv_unsigned r -> ew E i = getr regs r).
Proof.
intros E HE. pose proof fl_basic as (Hb & Hw & Hsum & HN0). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : SNK_STK = 9104) by reflexivity.
rewrite !HE by lia.
split; [exact F0_2|].
split; [rewrite (F0_reg 3 3%bv) by (cbv; first [discriminate | reflexivity]); exact G3|].
split; [rewrite (F0_reg 4 4%bv) by (cbv; first [discriminate | reflexivity]); exact G4|].
split; [change (ew F0 33) with (ew F0 (32 + 1)); rewrite F0_x; cbn [nth fl_extra]; apply unsigned_lit_small; lia|].
split; [change (ew F0 34) with (ew F0 (32 + 2)); rewrite F0_x; cbn [nth fl_extra]; apply unsigned_lit_small; lia|].
split; [change (ew F0 35) with (ew F0 (32 + 3)); rewrite F0_x; cbn [nth fl_extra]; apply unsigned_lit_small; lia|].
intros i r Hi Hr. pose proof (u5_range r). rewrite HE by lia. apply F0_reg; assumption.
Qed.
Definition KEEPq (m : word -> option byte) (X : Z -> Prop) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ fw_band sp0 OSP_PC a -> ~ fw_fc sp0 a -> ~ X a ->
aview tfibsegs (w_H W) m a = aview tfibsegs (w_H W) mem a.
Lemma KEEPq_step : forall m m' (X : Z -> Prop), KEEPq m X ->
(forall a, 0 <= a < 2 ^ 64 -> ~ fw_band sp0 OSP_PC a -> ~ fw_fc sp0 a ->
aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) -> KEEPq m' X.
Proof. intros m m' X HK H a H1 H2 H3 H4. rewrite (H a H1 H2 H3). exact (HK a H1 H2 H3 H4). Qed.
Definition QPOST := snk_post B ly S U W regs mem md sp0 (sp0 + OSP_PC) (fw_xw sp0 D M) 0
(fun mem' => SNK W mem' sp0 D N out 0).
Lemma fl_snk0 : (forall i, 0 <= i < b -> aview tfibsegs (w_H W) mem (sp0 + IBO + i) = Some (nth (Z.to_nat (w + i)) out 0)) /\
(forall i, 0 <= i < w -> aview tfibsegs (w_H W) mem (D + i) = Some (nth (Z.to_nat i) out 0)) /\
aview tfibsegs (w_H W) mem (D + w) = Some 0 /\ Forall (fun z => 0 <= z < 256) out.
Proof.
pose proof HSNK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SIB & SD & SDn & _ & _ & _ & _ & SF).
split; [exact SIB|]. split; [exact SD|]. split; [exact SDn | exact SF].
Qed.
Local Ltac vmr := vm_compute; reflexivity.
Local Ltac atoms := repeat match goal with H : bv_unsigned (ew ?E ?i) = _ |- context [bv_unsigned (ew ?E ?i)] => rewrite H end.
Local Ltac zfin := rewrite ?zcanon_id by (unfold M64; lia); unfold IBO, CKO, FO in *; lia.
Local Ltac dn := try unfold YG0d.w64; apply denot_U; uz; atoms; zfin.
Local Ltac bfin := repeat first [rewrite negb_true_iff | rewrite negb_false_iff];
  first [apply Z.ltb_ge | apply Z.ltb_lt | apply Z.eqb_neq | apply Z.eqb_eq]; lia.
Local Ltac btf := first [rewrite bt_ltu | rewrite bt_geu | rewrite bt_eq | rewrite bt_ne]; uz; atoms;
  rewrite ?zcanon_id by (unfold M64; lia); bfin.
Local Ltac nbf := unfold fw_band, fw_fc, OSP_PC, CKO, IBO, FO in *; lia.
Local Ltac sc := first [lia | nbf | (cbv beta; tauto) | (cbv beta; unfold IBO, CKO, FO in *; lia)].
Local Ltac mc_auto :=
  lazymatch goal with
  | |- ss_pc _ = _ => vmr
  | |- ss_resv _ = _ => reflexivity
  | |- ss_mem _ = _ :: _ => reflexivity
  | |- YP09.r_base _ = _ => reflexivity
  | |- YP09.r_lo _ = _ => reflexivity
  | |- YP09.r_hi _ = _ => reflexivity
  | |- - SNK_STK <= YP09.r_wlo _ => cbn; lia
  | |- YP09.r_whi _ <= 0 => cbn; lia
  | |- sr_get _ _ = _ => vmr
  | |- ss_atoms_lt _ _ = true => vmr
  | |- regions_wf _ = true => vmr
  | |- no_cdata _ = true => vmr
  | |- mem_atoms_lt _ _ = true => vmr
  | |- forallb _ _ = true => vmr
  | |- sv_denot _ _ = _ => dn
  | |- bv_unsigned (ew _ 2) = _ => assumption
  | |- ew _ 3 = _ => assumption
  | |- ew _ 4 = _ => assumption
  | |- _ mod _ = _ => reflexivity
  | |- ESTACK - SNK_STK <= _ => unfold ESTACK, SNK_STK; lia
  | |- _ <= OSP_PC => unfold OSP_PC; lia
  end.
Local Ltac mc_rest HI A2 :=
  lazymatch goal with
  | |- forall a, _ -> fw_xw _ _ _ a => let a := fresh "a" in intros a ?; unfold fw_xw, CKO, IBO, FO in *; lia
  | |- forall a, _ -> _ -> _ <= a < _ => let a := fresh "a" in intros a ? ?; unfold IBO in *; lia
  | |- forall a, _ -> writable_at _ _ a /\ _ =>
      let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      split; [apply (FWR _ _ a HI); lia | split; [apply HDw; lia | unfold ESTACK; lia]]
  | |- amem_range _ _ => first [ apply BAM; unfold IBO in *; lia | apply DAM; lia ]
  | |- range_addressable _ _ _ _ => first [ apply (BRA _ _ _ _ HI); unfold IBO in *; lia | apply (DRA _ _ _ _ HI); lia ]
  | |- 0 < _ -> shadow_hull_vis _ _ _ => intros ?;
      first [ apply (BHU _ _ _ _ HI); unfold IBO in *; lia | apply (DHU _ _ _ _ HI); lia ]
  | |- forall r a, In r _ -> _ -> 0 <= a < _ /\ _ =>
      let r := fresh "r" in let a := fresh "a" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in
      intros r a Hr Ha; cbn in Hr; destruct Hr as [<-|[<-|[]]];
      cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi] in Ha; rewrite A2 in Ha; unfold ESTACK, IBO in *; repeat split; lia
  | |- forall r a, In r _ -> _ -> apresent _ _ a =>
      let r := fresh "r" in let a := fresh "a" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in
      intros r a Hr Ha; cbn in Hr; destruct Hr as [<-|[<-|[]]];
      cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite A2 in Ha; apply (proj1 (proj2 (proj2 HI))); lia
  end.
Lemma srcq_buf : forall m (X : Z -> Prop), KEEPq m X -> (forall a, sp0 + IBO <= a < sp0 + IBO + b -> ~ X a) ->
forall a, sp0 + IBO <= a < sp0 + IBO + b -> aview tfibsegs (w_H W) m a <> None /\ ~ (sp0 + -432 - ESTACK <= a < sp0 + -432).
Proof.
intros m X HK HX a Ha. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof fl_basic as (Hb & Hw & Hsum & HN0).
pose proof fl_snk0 as (SIB & SD & SDn & SF).
assert (HVF : SNK_STK = 9104) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
split; [|unfold IBO in *; lia].
rewrite (HK a) by first [sc | apply HX, Ha].
replace a with (sp0 + IBO + (a - (sp0 + IBO))) by lia. rewrite (SIB (a - (sp0 + IBO))) by lia. discriminate.
Qed.
Local Ltac qfacts :=
  pose proof fl_basic as (Hb & Hw & Hsum & HN0); pose proof fl_snk0 as (SIB & SD & SDn & SF);
  pose proof (F0like_at F0 F0like_F0) as (A2 & A3 & A4 & A33 & A34 & A35 & AR);
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
  assert (HVF : SNK_STK = 9104) by reflexivity; assert (HES : ESTACK = 4096) by reflexivity.
(* b = 0: only the NUL store *)
Lemma fl_z : forall ms md1, b = 0 ->
st_ok tfibsegs F0 fZ1_s (restrict (w_H W) ms) -> FWIq (ms_mem ms) md1 -> KEEPq (ms_mem ms) (fun _ => False) ->
SRr tfibsegs W (mkCfg ms md1) QPOST.
Proof using All.
intros ms md1 Hb0 HS HI HK. qfacts.
eapply SRr_bind; [apply (PH F0 fZ1_s fZ1_e _ ms md1 HS r_fZ1); [discriminate | vmr | vmr | exact A2 | exact HI] |].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HI2 & HK2).
assert (R10 : getr (ms_regs ms2) 10 = Z_to_bv 64 (D + w)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) _ _ _ 10 HS2).
  replace (sr_get (ss_regs fZ1_e) 10) with (SOff 34 0) by vmr. dn. }
eapply SRr_bind; [apply (NUL F0 fZ1_e ms2 _ (D + w) HS2); [vmr | reflexivity | exact A2 | vmr | exact R10 | lia | exact HI2] |].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HI3 & HN3 & HO3).
eapply SRr_bind; [apply (PH F0 fZ2_s fZ2_e _ ms3 _ HS3 r_fZ2); [discriminate | vmr | vmr | exact A2 | exact HI3] |].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HI4 & HK4).
assert (KF : KEEPq (ms_mem ms4) (fun a => a = D + w)).
{ intros a Ha Hb' Hf Hx. rewrite (HK4 a Ha Hb' Hf). rewrite (HO3 a Ha); [| cbv beta in Hx; lia].
  rewrite (HK2 a Ha Hb' Hf). exact (HK a Ha Hb' Hf (fun f => f)). }
unfold QPOST.
apply (RET regs F0 fZ2_e ms4 _ 0 (SLit 0) _ HS4);
[reflexivity | vmr | exact A2 | exact AR | vmr | exact G1 | exact G2 | vmr | reflexivity | exact HI4 |].
apply (SNKI F0 fZ2_e ms4 N out 0 w (SOff 2 (-352)) (SOff 34 0) (SOff 35 0) HS4 A2);
[vmr | unfold w; lia | vmr | dn | vmr | dn | vmr | dn | | | | lia | lia | unfold w in *; lia | exact HN | exact SF].
- intros i Hi. lia.
- intros i Hi. rewrite (KF (D + i)) by sc. apply SD, Hi.
- rewrite (HK4 (D + w)) by sc. exact HN3.
Qed.
(* b <> 0: the buffer to the destination, then the NUL store *)
Lemma fl_n : forall ms md1, b <> 0 ->
st_ok tfibsegs F0 fN1_s (restrict (w_H W) ms) -> FWIq (ms_mem ms) md1 -> KEEPq (ms_mem ms) (fun _ => False) ->
SRr tfibsegs W (mkCfg ms md1) QPOST.
Proof using All.
intros ms md1 Hbn HS HI HK. qfacts.
eapply SRr_bind; [apply (PH F0 fN1_s fN1_e _ ms md1 HS r_fN1); [discriminate | vmr | vmr | exact A2 | exact HI] |].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HI2 & HK2).
assert (K2 : KEEPq (ms_mem ms2) (fun _ => False)) by (apply (KEEPq_step _ _ _ HK HK2)).
eapply SRr_bind.
{ eapply (MC F0 fN1_e ms2 _ _ _ 40 0x9231c (-432) 0 0 (SOff 34 0) (SOff 2 (-352)) (SOff 33 0) (D + w) (sp0 + IBO) b HS2).
  all: try mc_auto.
  all: try solve [unfold IBO in *; lia].
  all: try mc_rest HI2 A2.
  all: try exact HI2.
  apply (srcq_buf _ _ K2). intros; tauto. }
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HI3 & HP3 & Heff3 & Hfr3).
pose proof (F0like_at _ (F0like_havoc F0 40 (map (getr (ms_regs ms3)) CLOB) F0like_F0 (le_n 40)))
  as (B2 & B3 & B4 & B33 & B34 & B35 & BR).
eapply SRr_bind; [apply (PH _ fN2_s fN2_e _ ms3 _ HS3 r_fN2); [discriminate | vmr | vmr | exact B2 | exact HI3] |].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HI4 & HK4).
pose proof (st_ok_add_cond_neg tfibsegs _ _ _ BC_LTU (SAlu ALU_ADD (SMd M_MUL (SOff 33 0) (SLit (-1))) (SOff 35 0)) (SLit 0)
  HS4 ltac:(btf)) as HS4'.
eapply SRr_bind; [apply (PH _ fN3_s fN3_e _ ms4 _ HS4' r_fN3); [discriminate | vmr | vmr | exact B2 | exact HI4] |].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HI5 & HK5).
assert (R10 : getr (ms_regs ms5) 10 = Z_to_bv 64 (D + w + b)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) _ _ _ 10 HS5).
  replace (sr_get (ss_regs fN3_e) 10) with (SAlu ALU_ADD (SOff 33 0) (SOff 34 0)) by vmr. dn. }
eapply SRr_bind; [apply (NUL _ fN3_e ms5 _ (D + w + b) HS5); [vmr | reflexivity | exact B2 | vmr | exact R10 | lia | exact HI5] |].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HI6 & HN6 & HO6).
eapply SRr_bind; [apply (PH _ fN4_s fN4_e _ ms6 _ HS6 r_fN4); [discriminate | vmr | vmr | exact B2 | exact HI6] |].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HI7 & HK7).
assert (KF : KEEPq (ms_mem ms7) (fun a => D + w <= a <= D + w + b)).
{ intros a Ha Hb' Hf Hx. rewrite (HK7 a Ha Hb' Hf). rewrite (HO6 a Ha); [| cbv beta in Hx; lia].
  rewrite (HK5 a Ha Hb' Hf), (HK4 a Ha Hb' Hf). rewrite (Hfr3 a Ha); [| unfold fw_band, OSP_PC in Hb'; lia | cbv beta in Hx; lia].
  exact (K2 a Ha Hb' Hf (fun f => f)). }
assert (CP : forall i, 0 <= i < b -> aview tfibsegs (w_H W) (ms_mem ms7) (D + w + i) = Some (nth (Z.to_nat (w + i)) out 0)).
{ intros i Hi. rewrite (HK7 (D + w + i)) by sc. rewrite (HO6 (D + w + i)) by lia. rewrite (HK5 (D + w + i)) by sc.
  rewrite (HK4 (D + w + i)) by sc. rewrite (Heff3 i Hi). rewrite (K2 (sp0 + IBO + i)) by sc. apply SIB, Hi. }
assert (NL : aview tfibsegs (w_H W) (ms_mem ms7) (D + w + b) = Some 0) by (rewrite (HK7 (D + w + b)) by sc; exact HN6).
unfold QPOST.
apply (RET regs _ fN4_e ms7 _ 0 (SLit 0) _ HS7);
[reflexivity | vmr | exact B2 | exact BR | vmr | exact G1 | exact G2 | vmr | reflexivity | exact HI7 |].
apply (SNKI _ fN4_e ms7 N out 0 (w + b) (SOff 2 (-352)) (SAlu ALU_ADD (SOff 33 0) (SOff 34 0))
  (SAlu ALU_ADD (SMd M_MUL (SOff 33 0) (SLit (-1))) (SOff 35 0)) HS7 B2);
[vmr | unfold w; lia | vmr | dn | vmr | dn | vmr | dn | | | | lia | lia | unfold w in *; lia | exact HN | exact SF].
- intros i Hi. lia.
- intros i Hi. destruct (Z_lt_le_dec i w) as [Hiw|Hiw].
  + rewrite (KF (D + i)) by sc. apply SD. lia.
  + replace (D + i) with (D + w + (i - w)) by lia. rewrite CP by lia. replace (w + (i - w)) with i by lia. reflexivity.
- replace (D + (w + b)) with (D + w + b) by lia. exact NL.
Qed.
Lemma fl_main : SRr tfibsegs W (cfg_at tfibsegs A_SNW regs mem md) QPOST.
Proof using All.
qfacts.
pose proof fl_entry_ok as HS0.
unfold cfg_at. change (YG0d.w64 A_SNW) with (Z_to_bv 64 A_SNW).
eapply SRr_bind; [apply (PH F0 f1_s f1_e _ _ md HS0 r_f1); [discriminate | vmr | vmr | exact A2 | exact FINIT] |].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HI1 & HK1).
pose proof (st_ok_add_cond_neg tfibsegs F0 _ _ BC_LTU (SOff 35 0) (SOff 33 0) HS1 ltac:(btf)) as HS1'.
eapply SRr_bind; [apply (PH F0 f2_s f2_e _ ms1 _ HS1' r_f2); [discriminate | vmr | vmr | exact A2 | exact HI1] |].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HI2 & HK2).
assert (K2 : KEEPq (ms_mem ms2) (fun _ => False)).
{ intros a Ha Hb' Hf _. rewrite (HK2 a Ha Hb' Hf). exact (HK1 a Ha Hb' Hf). }
destruct (Z.eq_dec b 0) as [Hb0|Hbn].
- apply (fl_z ms2 _ Hb0); [| exact HI2 | exact K2].
  exact (st_ok_add_cond tfibsegs F0 _ _ BC_EQ (SOff 33 0) (SLit 0) HS2 ltac:(btf)).
- apply (fl_n ms2 _ Hbn); [| exact HI2 | exact K2].
  exact (st_ok_add_cond_neg tfibsegs F0 _ _ BC_EQ (SOff 33 0) (SLit 0) HS2 ltac:(btf)).
Qed.
End q.
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem asnflush_realizes : forall B, AR_laws tfibsegs B -> TfibSyms B -> aintrin_realizesU B OCpy W_MEMCPY ->
asnflush_realizesU B A_SNW.
Proof.
intros B LAWS TB AMEMCPY. unfold asnflush_realizesU.
intros ly S U W regs mem md sp0 D N M out b HB HR G10 G11 G12 HSNK HDst HRM.
destruct HB as (HAR & Hac & Hsp44 & Hsp16 & Hstk & Htop & Hsp47 & Hhigh & Hpres & Hzsh).
destruct HR as (G1 & G2 & G3 & G4).
destruct HDst as (HD0 & HDac & HM & Hcan & HDw & HDam & HDra & HDhu).
pose proof HSNK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HN & _).
exact (fl_main B LAWS TB AMEMCPY ly S U W regs mem md sp0 D N M out b HAR Hac Hsp44 Hsp16 Hstk Htop Hsp47 Hhigh
  Hpres Hzsh G1 G2 G3 G4 G10 G11 G12 HSNK HD0 HDac HM Hcan HDw HDam HDra HDhu HRM HN).
Qed.
End t.
