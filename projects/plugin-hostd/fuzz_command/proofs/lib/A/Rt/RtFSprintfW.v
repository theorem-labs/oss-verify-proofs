(* The sprintf walk from the trampoline 0x45180 to the vsnprintf interceptor's return: run A, printf_common under its
   shared contract, run B through musl vsprintf and the vsnprintf trampoline 0x45178, the vsnprintf interceptor 0x49858 under its shared contract (an
   FP-existential post, continued with RtPFSx.srr_fx_continue), then RtFSprintfE.spf_after. The two contracts
   (RtPFSx.v:65 sh_apcommon_realizesUz, RtPFSx.v:166 sh_avsnprintf_icpt_realizesUa, from fuzz_manifest) and the check
   site's interface are Section hypotheses here; RtFSprintf.v discharges the check site and names the two contracts. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE20 AE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtPFupoison RtPFPf RtPFShared RtPFSx RtPFCmd.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtFSprintfTbl RtFSprintfRun RtFSprintfK RtFSprintfFF.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtFSprintfE.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtPFCv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the callees' windows (printf_common at 0x48cdc, the vsnprintf interceptor at 0x49858), both entered at the entry
   sp - 2240: 2240 + 2 * ESTACK = 10,432 <= CMD_SP_K = 3 * ESTACK *)
Definition SP_KPC : Z := ESTACK.
Definition SP_KVS : Z := 2 * ESTACK.
(* musl vsprintf's size argument *)
Definition SP_N : Z := 0x7fffffff.
Lemma sn_sp : forall T, Z.of_nat (length T) < 2 ^ 31 - 1 -> sn_len (SP_N - 1) T = sp_len T /\ sn_bytes (SP_N - 1) T = sp_bytes T.
Proof. intros T HT. split; [exact (sp_len_sn T HT) | exact (sp_bytes_sn T HT)]. Qed.

Ltac bvr := match goal with |- 0 <= bv_unsigned ?b < _ =>
  let Hbvr := fresh "Hbvr" in pose proof (bv_unsigned_in_range 64 b) as Hbvr;
  change (bv_modulus 64) with (2 ^ 64) in Hbvr; exact Hbvr end.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : CmdBSyms B.
Variable scr : Z.
Hypothesis Hscr : 0 <= scr <= ESTACK.
Hypothesis CHK : forall fx0 : YK11.FPState, @spf_chk fx0 rc B scr.
(* omx-clap-core/fuzz_manifest's published contracts at this image (RtPFSx.v: printf_common's
   sh_apcommon_realizesUz, proved upstream as RT_pf_shU.pcom_shz for 2320 <= K; the vsnprintf interceptor's
   sh_avsnprintf_icpt_realizesUa, proved upstream as FMsnprintfSvsni.svsni_ok) *)
Hypothesis APCOMMON : sh_apcommon_realizesUz tfibsegs B FR_cmd SP_KPC CMD_SP_CR SP_PCOM.
Hypothesis AVSNI : sh_avsnprintf_icpt_realizesUa tfibsegs B FR_cmd SP_KVS CMD_GOTW CMD_GUARD CMD_IMG_LO CMD_IMG_HI
  CMD_SP_CR SP_VSNI.
#[local] Notation H W := (w_H W).

Section w.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (d f : Z) (xs ws T : list Z) (cval : Z).
Hypothesis HPRE : ecall_pre tfibsegs B ly S W regs mem md.
Hypothesis HKlo : ly_stk_lo ly + CMD_SP_K <= spZ regs.
Hypothesis HKp : forall a, spZ regs - CMD_SP_K <= a < spZ regs -> apresent (H W) mem a.
Hypothesis R10 : getr regs 10 = w64 d.
Hypothesis R11 : getr regs 11 = w64 f.
Hypothesis Hcv : consts_view tfibsegs W mem CMD_SP_CR.
Hypothesis Hcb : Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) CMD_SP_CR.
Hypothesis Hcd : Forall (fun r => Forall (zdisjoint r) (snp_out CMD_SP_K (spZ regs) d (sp_len T))) CMD_SP_CR.
Hypothesis Hgc : rdword (aview tfibsegs (H W) mem) CMD_GOTW = Some CMD_GUARD.
Hypothesis Hgv : rdword (aview tfibsegs (H W) mem) CMD_GUARD = Some cval.
Hypothesis Hgcd : Forall (zdisjoint (CMD_GOTW, 8)) (snp_out CMD_SP_K (spZ regs) d (sp_len T)).
Hypothesis Hgvd : Forall (zdisjoint (CMD_GUARD, 8)) (snp_out CMD_SP_K (spZ regs) d (sp_len T)).
Hypothesis Hva : va_words2 regs (aview tfibsegs (H W) mem) (spZ regs) xs ws.
Hypothesis Hxs : spZ regs + 8 * Z.of_nat (length xs) < 2 ^ 63.
Hypothesis Hxsd : Forall (zdisjoint (spZ regs, 8 * Z.of_nat (length xs))) (snp_out CMD_SP_K (spZ regs) d (sp_len T)).
Hypothesis HFF : FR_cmd (aview tfibsegs (H W) mem) (snp_out CMD_SP_K (spZ regs) d (sp_len T)) f ws T.
Hypothesis HT : Z.of_nat (length T) < 2 ^ 31 - 1.
Hypothesis Hd0 : 0 < d.
Hypothesis Hdw : d + sp_len T <= 2 ^ 63.
Hypothesis Hpw : pairwise zdisjoint (snp_out CMD_SP_K (spZ regs) d (sp_len T)).
Hypothesis Hdst : dest_ok tfibsegs B ly S W regs mem d (sp_len T).
Hypothesis Ham : amem_range d (sp_len T).
Hypothesis Hra : range_addressable (aview tfibsegs (H W) mem) SHADOW_OFF d (sp_len T).
Hypothesis Hhull : shadow_hull_vis (aview tfibsegs (H W) mem) d (sp_len T).
Hypothesis Hdog : zdisjoint (d, sp_len T) (CMD_IMG_LO, CMD_IMG_HI - CMD_IMG_LO).
Hypothesis Hfrm : Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0.
Hypothesis H47 : spZ regs + 8 * Z.of_nat (length xs) <= 2 ^ 47.
Hypothesis Hd8 : amem_range d (sp_len T + 8).

Definition POST : world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
c' = @cfg_at fx' tfibsegs (raZ regs) regs' mem' md' /\
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
AR tfibsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (Z.of_nat (length T)) /\
(forall i, 0 <= i < sp_len T -> aview tfibsegs (H W) mem' (d + i) = Some (nth (Z.to_nat i) (sp_bytes T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sp_len T) ->
~ (spZ regs - CMD_SP_K <= a < spZ regs) -> aview tfibsegs (H W) mem' a = aview tfibsegs (H W) mem a) /\
(forall a, apresent (H W) mem a -> apresent (H W) mem' a).

Let sp0 : Z := spZ regs.
Let w : Z := sp_len T.
Definition ap : Z := spZ regs - 48.

Lemma basw : kHighMemBeg <= sp0 - spK /\ sp0 <= 2 ^ 47 /\ sp0 mod 16 = 0 /\
  ly_stk_lo ly <= sp0 - spK /\ sp0 <= ly_stk_hi ly /\ 1 <= w /\ w = Z.of_nat (length T) + 1 /\
  d + w <= 2 ^ 47 - 1 /\ (d + w <= sp0 - spK \/ sp0 + 8 * Z.of_nat (length xs) <= d) /\
  ws = map (argZ regs) [2; 3; 4; 5; 6; 7] ++ xs.
Proof.
pose proof HPRE as (HA & _ & H16 & _ & Hhi & _).
pose proof (stk_kHighMemBeg B ly S _ (proj1 HA)) as [K1 K2].
pose proof Hva as (Hws & _).
apply pairwise_snp in Hpw. apply Forall_snp in Hxsd as [_ X2].
unfold sp0, w, sp_len in *. unfold zdisjoint in *. cbn [fst snd] in *.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, spK, CMD_SP_K, ESTACK in *.
split; [lia|]. split; [lia|]. split; [exact H16|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [lia|]. split; [lia | exact Hws].
Qed.
Ltac zl := cbv beta in *; unfold sp0, w, ap, spK, CMD_SP_K, SP_KPC, SP_KVS, ESTACK, SP_FR, SP_STK, kHighMemBeg,
  kHighMemEnd, TFIB_IMG_END, SHADOW_OFF, kLowMemEnd in *; lia.

Lemma aft : aft_pre B ly S W regs mem md d T.
Proof.
pose proof HPRE as (HA & Hret & H16 & _ & Hhi & _ & Hgp & Htp).
pose proof basw as (B1 & B2 & B3 & L1 & L2 & Hw1 & Hwl & Hdw' & Hdj & _).
apply pairwise_snp in Hpw.
unfold aft_pre. split; [exact HA|].
split; [unfold spK; exact HKlo|]. split; [exact Hhi|]. split; [exact H16|]. split; [exact Hret|].
split; [exact Hgp|]. split; [exact Htp|]. split; [exact R10|]. split; [exact HT|]. split; [exact Hd0|].
split; [exact Hdw|]. split; [exact Hpw|]. split; [exact Ham|]. split; [exact Hra | exact Hhull].
Qed.

(* ---- what a memory the walk changed only inside its window [sp0 - K, sp0) keeps ---- *)
Definition INV0 (m : word -> option byte) (md' : Model) : Prop :=
  fr_inv B ly S W mem md (sp0 - spK) sp0 (fun _ => False) m md'.
Lemma av0 : forall m md', INV0 m md' -> forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - spK <= a < sp0) ->
  aview tfibsegs (H W) m a = aview tfibsegs (H W) mem a.
Proof. intros m md' (_ & _ & _ & Hfr & _) a Ha Hn. exact (Hfr a Ha Hn (fun X => X)). Qed.
Lemma cr_out : forall a, Exists (in_zr a) CMD_SP_CR ->
  0 <= a < 2 ^ 63 /\ ~ (sp0 - spK <= a < sp0) /\ ~ (d <= a < d + w).
Proof.
intros a Ha. apply Exists_exists in Ha as (r & Hr & Hin).
pose proof (proj1 (Forall_forall _ _) Hcb r Hr) as (Hb1 & Hb2).
pose proof (proj1 (Forall_forall _ _) Hcd r Hr) as Hd. apply Forall_snp in Hd as [D1 D2].
unfold in_zr, zdisjoint in *. cbn [fst snd] in *. unfold sp0, w, spK, CMD_SP_K in *. lia.
Qed.
Lemma cv0 : forall m md', INV0 m md' -> consts_view tfibsegs W m CMD_SP_CR.
Proof.
intros m md' HI a Ha. destruct (cr_out a Ha) as (C1 & C2 & _). rewrite (av0 m md' HI a ltac:(lia) C2). exact (Hcv a Ha).
Qed.
Lemma rdw0 : forall m md' p v, INV0 m md' -> 0 <= p -> p + 8 <= 2 ^ 63 -> zdisjoint (p, 8) (sp0 - spK, spK) ->
  rdword (aview tfibsegs (H W) mem) p = Some v -> rdword (aview tfibsegs (H W) m) p = Some v.
Proof.
intros m md' p v HI P1 P2 Hdj Hr. apply (rdword_same (aview tfibsegs (H W) mem)); [|exact Hr].
intros a Ha. apply (av0 m md' HI); [lia|]. unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. lia.
Qed.
Lemma ff0 : forall m md', INV0 m md' -> FR_cmd (aview tfibsegs (H W) m) (snp_out CMD_SP_K sp0 d w) f ws T.
Proof.
intros m md' HI. apply (FR_cmd_stable64 (aview tfibsegs (H W) mem)); [exact HFF|].
intros a Ha. destruct (Z_lt_le_dec a (sp0 - spK)) as [L|L]; [left; apply (av0 m md' HI); [exact Ha | lia]|].
destruct (Z_lt_le_dec a sp0) as [L'|L']; [|left; apply (av0 m md' HI); [exact Ha | lia]].
right. split.
- apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. unfold sp0, spK, CMD_SP_K in *. lia.
- pose proof basw as (B1 & _). unfold SHADOW_OFF, kHighMemBeg in *. lia.
Qed.
(* the format family over a window inside the walk's *)
Lemma ff_sub : forall m md' lo K', INV0 m md' -> sp0 - spK <= lo -> lo + K' <= sp0 ->
  FR_cmd (aview tfibsegs (H W) m) [(lo, K'); (d, w)] f ws T.
Proof.
intros m md' lo K' HI L1 L2. apply (FR_cmd_mono _ (snp_out CMD_SP_K sp0 d w)); [exact (ff0 m md' HI)|].
intros r' Hr'. destruct Hr' as [<-|[<-|[]]].
- exists (sp0 - CMD_SP_K, CMD_SP_K). split; [left; reflexivity | cbn [fst snd]; unfold spK, CMD_SP_K in *; lia].
- exists (d, w). split; [right; left; reflexivity | cbn [fst snd]; lia].
Qed.
Lemma xs0 : forall m md', INV0 m md' -> words_at (aview tfibsegs (H W) m) sp0 xs.
Proof.
intros m md' HI. pose proof Hva as (_ & Hx). apply (words_at_same (aview tfibsegs (H W) mem)); [|exact Hx].
intros a Ha. pose proof basw as (B1 & _). apply (av0 m md' HI); zl.
Qed.
(* the va words: a2 .. a7 at ap from six saved words, then the caller's xs at sp0 *)
Lemma ws0 : forall m md', INV0 m md' ->
  (forall k, (k < 6)%nat -> val_mem tfibsegs (mrestrict (H W) m) (ap + 8 * Z.of_nat k) 8
     (bv_unsigned (getr regs (Z_to_bv 5 (12 + Z.of_nat k))))) ->
  words_at (aview tfibsegs (H W) m) ap ws.
Proof.
intros m md' HI HV. pose proof basw as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hws). rewrite Hws.
assert (V : forall (k : nat) (o r : Z), (k < 6)%nat -> o = 8 * Z.of_nat k -> r = 12 + Z.of_nat k ->
  val_mem tfibsegs (mrestrict (H W) m) (ap + o) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))).
{ intros k o r Hk -> ->. exact (HV k Hk). }
apply words_at_app.
- cbn [map]. unfold argZ. apply words6; try bvr.
  + exact (V 0%nat 0 12 ltac:(lia) eq_refl eq_refl).
  + exact (V 1%nat 8 13 ltac:(lia) eq_refl eq_refl).
  + exact (V 2%nat 16 14 ltac:(lia) eq_refl eq_refl).
  + exact (V 3%nat 24 15 ltac:(lia) eq_refl eq_refl).
  + exact (V 4%nat 32 16 ltac:(lia) eq_refl eq_refl).
  + exact (V 5%nat 40 17 ltac:(lia) eq_refl eq_refl).
- cbn [length map]. replace (ap + 8 * Z.of_nat 6) with sp0 by (unfold ap, sp0; lia). exact (xs0 m md' HI).
Qed.
Lemma ws_len : 8 * Z.of_nat (length ws) = 48 + 8 * Z.of_nat (length xs).
Proof. pose proof basw as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hws). rewrite Hws, length_app. cbn [length map]. lia. Qed.
(* the destination at a callee's sp inside the window *)
Lemma dest0 : forall m md' (regs' : bvmap 5 word), INV0 m md' -> sp0 - spK + ESTACK <= spZ regs' <= sp0 ->
  dest_ok tfibsegs B ly S W regs' m d w.
Proof.
intros m md' regs' HI Hs a Ha. pose proof basw as (_ & _ & _ & _ & _ & _ & _ & _ & Hdj & _).
destruct (Hdst a Ha) as (Hw & Ho & _). pose proof HI as (_ & _ & _ & _ & Hpm).
split; [exact (writable_xfer (H W) mem m a Hw (Hpm a))|]. split; [exact Ho|]. unfold sp0, w in *. lia.
Qed.
Lemma sh0 : forall m md', INV0 m md' ->
  range_addressable (aview tfibsegs (H W) m) SHADOW_OFF d w /\ shadow_hull_vis (aview tfibsegs (H W) m) d w.
Proof.
intros m md' HI.
apply (shadow_pair_stable (aview tfibsegs (H W) mem) (aview tfibsegs (H W) m) d w); [|lia | exact Ham | exact Hra | exact Hhull].
intros s Hs. pose proof basw as (B1 & _). apply (av0 m md' HI); zl.
Qed.
Lemma ecall0 : forall m md' (regs' : bvmap 5 word), INV0 m md' -> YK0s.ret_ok (getr regs' 1) ->
  spZ regs' = sp0 - SP_FR -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  ecall_pre tfibsegs B ly S W regs' m md'.
Proof.
intros m md' regs' HI Hret Hsp G3 G4. pose proof HI as (HA & _ & Hp & _).
pose proof basw as (B1 & B2 & B3 & L1 & L2 & _). pose proof HPRE as (_ & _ & _ & _ & _ & _ & Hgp & Htp).
split; [exact HA|]. split; [exact Hret|].
split; [rewrite Hsp; replace (sp0 - SP_FR) with (sp0 + (-140) * 16) by (unfold SP_FR; lia); rewrite Z_mod_plus_full; exact B3|].
split; [rewrite Hsp; zl|]. split; [rewrite Hsp; zl|]. split; [intros a Ha; rewrite Hsp in Ha; apply Hp; zl|].
split; [rewrite G3; exact Hgp | rewrite G4; exact Htp].
Qed.

(* ---- the vsnprintf interceptor, at the end of run B, and the rest of the walk ---- *)
Lemma vsn_call : forall E1 ms md1,
  st_ok tfibsegs E1 eB (restrict (H W) ms) -> EOK regs E1 -> INV0 (ms_mem ms) md1 ->
  SRr tfibsegs W (mkCfg ms md1) POST.
Proof.
intros E1 ms md1 HS HE HI.
pose proof basw as (B1 & B2 & B3 & L1 & L2 & Hw1 & Hwl & Hdw' & Hdj & Hws).
pose proof HPRE as (_ & _ & _ & _ & _ & _ & Hgp & Htp).
assert (E2 : bv_unsigned (ew E1 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (RG : forall (r : bv 5) v, sr_get (ss_regs eB) r = v -> getr (ms_regs ms) r = sv_denot E1 v)
  by (intros r v Hv; exact (spf_reg W E1 eB ms r v HS Hv)).
pose proof (st_ok_restrict_mkst tfibsegs (H W) E1 _ _ HS ltac:(vm_compute; reflexivity)) as Hshape.
set (regsB := ms_regs ms) in *. set (memB := ms_mem ms) in *.
assert (SP : spZ regsB = sp0 - SP_FR).
{ unfold spZ at 1. subst regsB. rewrite (RG 2%bv (SOff 2 (- SP_FR))) by (vm_compute; reflexivity). cbn [sv_denot]. rewrite E2.
  rewrite unsigned_lit_small by zl. lia. }
assert (RA : getr regsB 1 = Z_to_bv 64 SP_RA_VSN) by (subst regsB; rewrite (RG 1%bv (SLit SP_RA_VSN)) by (vm_compute; reflexivity); reflexivity).
assert (A10 : getr regsB 10 = w64 d).
{ subst regsB. rewrite (RG 10%bv (SOff 10 0)) by (vm_compute; reflexivity). apply den_atom0'. rewrite (HE 10%nat 10%bv eq_refl). exact R10. }
assert (A11 : getr regsB 11 = w64 SP_N) by (subst regsB; rewrite (RG 11%bv (SLit 2147483647)) by (vm_compute; reflexivity); reflexivity).
assert (A12 : getr regsB 12 = w64 f).
{ subst regsB. rewrite (RG 12%bv (SOff 11 0)) by (vm_compute; reflexivity). apply den_atom0'. rewrite (HE 11%nat 11%bv eq_refl). exact R11. }
assert (A13 : getr regsB 13 = w64 ap).
{ subst regsB. rewrite (RG 13%bv (SOff 2 (-48))) by (vm_compute; reflexivity). cbn [sv_denot]. rewrite E2. reflexivity. }
assert (A3 : getr regsB 3 = getr regs 3).
{ subst regsB. rewrite (RG 3%bv (SOff 3 0)) by (vm_compute; reflexivity). apply den_atom0'. exact (HE 3%nat 3%bv eq_refl). }
assert (A4 : getr regsB 4 = getr regs 4).
{ subst regsB. rewrite (RG 4%bv (SOff 4 0)) by (vm_compute; reflexivity). apply den_atom0'. exact (HE 4%nat 4%bv eq_refl). }
(* the va words from the saved a2 .. a7 *)
assert (HV : forall k, (k < 6)%nat -> val_mem tfibsegs (mrestrict (H W) memB) (ap + 8 * Z.of_nat k) 8
  (bv_unsigned (getr regs (Z_to_bv 5 (12 + Z.of_nat k))))).
{ intros k Hk. replace (ap + 8 * Z.of_nat k) with (bv_unsigned (ew E1 2) + (-48 + 8 * Z.of_nat k)) by (rewrite E2; unfold ap, sp0; lia).
  subst memB. apply (slot_of W E1 eB ms (- SP_FR) (- SP_FR) _ (SOff (Z.to_nat (12 + Z.of_nat k)) 0)).
  - exact HS.
  - vm_compute. reflexivity.
  - do 6 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
  - apply den_atom0'. rewrite (EOK_r regs E1 (12 + Z.of_nat k) HE ltac:(lia)). symmetry. apply Z_to_bv_bv_unsigned.
  - bvr. }
pose proof (ws0 memB md1 HI HV) as Hwords.
pose proof ws_len as WL.
destruct (sn_sp T HT) as [SN1 SN2].
destruct (sh0 memB md1 HI) as [Hra1 Hhull1].
pose proof HI as (HA1 & _ & Hp1 & _).
(* the contract *)
assert (HC : SRr tfibsegs W (cfg_at tfibsegs SP_VSNI regsB memB md1)
  (fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
    c' = @cfg_at fx' tfibsegs (raZ regsB) regs' mem' md' /\
    (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
    Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
    ARU tfibsegs B ly S [] W mem' md' /\ aregs_preserved regsB regs' /\ same_but_materialized md1 md' /\
    getr regs' 10 = w64 (Z.of_nat (length T)) /\
    (forall i, 0 <= i < sn_len (SP_N - 1) T ->
       aview tfibsegs (H W) mem' (d + i) = Some (nth (Z.to_nat i) (sn_bytes (SP_N - 1) T) 0)) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (SP_N - 1) T) ->
       ~ (spZ regsB - SP_KVS <= a < spZ regsB) -> aview tfibsegs (H W) mem' a = aview tfibsegs (H W) memB a) /\
    (forall a, apresent (H W) memB a -> apresent (H W) mem' a))).
{ apply (AVSNI ly S [] W regsB memB md1 d SP_N f ap ws T cval).
  - apply ecall_preU_nil.
    apply (ecall0 memB md1 regsB HI); [rewrite RA; apply ret_ok_lit; [unfold SP_RA_VSN; lia | reflexivity] | exact SP | exact A3 | exact A4].
  - rewrite SP. zl.
  - intros a Ha. rewrite SP in Ha. apply Hp1. zl.
  - exact A10.
  - exact A11.
  - exact A12.
  - exact A13.
  - exact (cv0 memB md1 HI).
  - exact Hcb.
  - rewrite SN1. apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) Hcd r Hr) as X.
    apply Forall_snp in X as [X1 X2]. apply Forall_snp. split; [|exact X2].
    apply (zdisjoint_sub r (sp0 - CMD_SP_K, CMD_SP_K)); [exact X1 | cbn [fst snd]; rewrite SP; zl | cbn [fst snd]; rewrite SP; zl].
  - apply (rdw0 memB md1 _ _ HI); [unfold CMD_GOTW; lia | unfold CMD_GOTW; lia | | exact Hgc].
    apply Forall_snp in Hgcd as [X1 _]. exact X1.
  - apply (rdw0 memB md1 _ _ HI); [unfold CMD_GUARD; lia | unfold CMD_GUARD; lia | | exact Hgv].
    apply Forall_snp in Hgvd as [X1 _]. exact X1.
  - unfold CMD_GOTW; lia.
  - unfold CMD_GOTW; lia.
  - unfold CMD_GUARD; lia.
  - unfold CMD_GUARD; lia.
  - rewrite SN1. apply Forall_snp in Hgcd as [X1 X2]. apply Forall_snp. split; [|exact X2].
    apply (zdisjoint_sub _ (sp0 - CMD_SP_K, CMD_SP_K)); [exact X1 | cbn [fst snd]; rewrite SP; zl | cbn [fst snd]; rewrite SP; zl].
  - rewrite SN1. apply Forall_snp in Hgvd as [X1 X2]. apply Forall_snp. split; [|exact X2].
    apply (zdisjoint_sub _ (sp0 - CMD_SP_K, CMD_SP_K)); [exact X1 | cbn [fst snd]; rewrite SP; zl | cbn [fst snd]; rewrite SP; zl].
  - exact Hwords.
  - zl.
  - rewrite WL. unfold ap. zl.
  - rewrite SN1, WL. apply Forall_snp. unfold zdisjoint. cbn [fst snd]. rewrite SP. unfold ap. split; zl.
  - rewrite SN1, SP. apply (ff_sub memB md1 _ _ HI); zl.
  - unfold SP_N. lia.
  - exact HT.
  - exact Hd0.
  - rewrite SN1. exact Hdw.
  - rewrite SN1. apply pairwise_snp. unfold zdisjoint. cbn [fst snd]. rewrite SP. zl.
  - rewrite SN1. apply (dest0 memB md1 regsB HI). rewrite SP. zl.
  - rewrite SN1. exact Ham.
  - rewrite SN1. exact Hra1.
  - rewrite SN1. exact Hhull1.
  - rewrite SN1. exact Hdog.
  - exact Hfrm.
  (* the GXA-route premises: the va area at or above the callee's sp, the destination below its window or above the
     va area (the contract keeps d off the window and off the caller's slots), the slots below 2^47, the slack word *)
  - rewrite SP. unfold ap. zl.
  - rewrite SN1, WL, SP. destruct Hdj as [X|X]; [left; zl | right; unfold ap; zl].
  - rewrite WL. unfold ap. zl.
  - rewrite SN1. exact Hd8. }
rewrite Hshape.
change (mkCfg (mkst regsB (Z_to_bv 64 (ss_pc eB)) memB (seg_rom tfibsegs)) md1) with (cfg_at tfibsegs SP_VSNI regsB memB md1).
apply (srr_fx_continue tfibsegs W _ (raZ regsB)
  (fun (fx' : YK11.FPState) regs' mem' md' => ARU tfibsegs B ly S [] W mem' md' /\ aregs_preserved regsB regs' /\
     same_but_materialized md1 md' /\ getr regs' 10 = w64 (Z.of_nat (length T)) /\
     (forall i, 0 <= i < sn_len (SP_N - 1) T ->
        aview tfibsegs (H W) mem' (d + i) = Some (nth (Z.to_nat i) (sn_bytes (SP_N - 1) T) 0)) /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (SP_N - 1) T) ->
        ~ (spZ regsB - SP_KVS <= a < spZ regsB) -> aview tfibsegs (H W) mem' a = aview tfibsegs (H W) memB a) /\
     (forall a, apresent (H W) memB a -> apresent (H W) mem' a)) POST HC).
intros fx' regs' mem' md' FP1 FP2 (HA' & Hap & Hsb & R10' & HBY & Hfr & Hpr).
apply ARU_nil in HA'.
rewrite SN1, SN2 in *.
assert (RAZ : raZ regsB = SP_RA_VSN) by (unfold raZ; rewrite RA; apply unsigned_lit_small; unfold SP_RA_VSN; lia).
rewrite RAZ.
(* the symbolic state at fx' after the call *)
assert (HSB' : st_ok (fx:=fx') tfibsegs E1 eB (mkst (fx:=fx') regsB (Z_to_bv 64 (ss_pc eB)) (mrestrict (H W) memB) (seg_rom tfibsegs))).
{ apply (st_ok_fx fx). rewrite Hshape in HS. rewrite restrict_mkst_fx in HS. exact HS. }
pose proof memC_ok as (MC1 & MC2 & MC3).
set (E2' := havoc E1 48 (map (getr regs') CLOB)).
assert (HS2 : st_ok (fx:=fx') tfibsegs E2' ssC
  (restrict (w_H W) (mkst (fx:=fx') regs' (Z_to_bv 64 SP_RA_VSN) mem' (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx.
  exact (st_ok_after_call (fx:=fx') tfibsegs 48 E1 eB _ regs' (mrestrict (H W) mem') (ss_mem eB) SP_RA_VSN HSB'
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) MC1 MC2 MC3 (submem_refl _)
    ltac:(vm_compute; reflexivity) (regs_preserved_of_a regsB regs' Hap)
    ltac:(rewrite eB_mem_shape;
          apply Forall_cons;
          [ apply (kept_stack W E1 memB mem' sp0 (- SP_FR) (- SP_FR) _ E2); [zl | zl | lia | |];
            [ intros a Ha; apply Hfr; zl
            | intros a Ha; apply Hpr; apply Hp1; zl ]
          | apply Forall_forall; intros r Hr; apply (kept_ro W E1 memB mem' r Hr); intros a Ha; apply Hfr;
            [ lia | unfold zdisjoint, CMD_IMG_LO, CMD_IMG_HI in Hdog; cbn [fst snd] in Hdog; lia | rewrite SP; zl ] ])). }
assert (HE2 : EOK regs E2') by (apply EOK_havoc; [exact HE | lia]).
assert (H52 : ew E2' 52 = w64 (Z.of_nat (length T))).
{ subst E2'. change 52%nat with (48 + 4)%nat. rewrite (ew_havoc_new E1 48 _ 4 (Z_to_bv 64 0)) by (cbn; lia). cbn. exact R10'. }
assert (HI2 : INV B ly S W regs mem md d T mem' md').
{ apply (fr_step B ly S W mem md _ _ (XWd d T) memB md1 mem' md').
  - apply (fr_mono B ly S W mem md _ _ (fun _ => False) (XWd d T) memB md1 HI). intros a [].
  - exact HA'.
  - exact Hsb.
  - intros a Ha. apply Hpr. apply Hp1. exact Ha.
  - intros a Ha H1 H2. apply Hfr; [exact Ha | exact H2 | rewrite SP; zl].
  - exact Hpr. }
unfold cfg_at. change (w64 SP_RA_VSN) with (Z_to_bv 64 SP_RA_VSN).
eapply SRr_mono.
{ exact (@spf_after fx' rc B LAWS scr Hscr (CHK fx') ly S W regs mem md d T aft E2'
    (mkst (fx:=fx') regs' (Z_to_bv 64 SP_RA_VSN) mem' (seg_rom tfibsegs)) md' HS2 HE2 H52 HI2 HBY). }
intros W' c' _ (-> & regs'' & mem'' & md'' & -> & HA'' & Hap'' & Hsb'' & R10'' & HBY'' & Hfr'' & Hpr'').
unfold POST. split; [reflexivity|].
exists fx', regs'', mem'', md''. split; [reflexivity|]. split; [exact FP1|]. split; [exact FP2|].
split; [exact HA''|]. split; [exact Hap''|]. split; [exact Hsb''|]. split; [exact R10''|].
split; [exact HBY''|]. split; [exact Hfr'' | exact Hpr''].
Qed.

(* ---- printf_common at the end of run A, then run B to the vsnprintf trampoline ---- *)
Lemma pcom_call : forall E0 ms md1,
  st_ok tfibsegs E0 eA (restrict (H W) ms) -> EOK regs E0 -> INV0 (ms_mem ms) md1 ->
  SRr tfibsegs W (mkCfg ms md1) POST.
Proof.
intros E0 ms md1 HS HE HI.
pose proof basw as (B1 & B2 & B3 & L1 & L2 & Hw1 & Hwl & Hdw' & Hdj & Hws).
assert (E2 : bv_unsigned (ew E0 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (RG : forall (r : bv 5) v, sr_get (ss_regs eA) r = v -> getr (ms_regs ms) r = sv_denot E0 v)
  by (intros r v Hv; exact (spf_reg W E0 eA ms r v HS Hv)).
pose proof (st_ok_restrict_mkst tfibsegs (H W) E0 _ _ HS ltac:(vm_compute; reflexivity)) as Hshape.
assert (HV : forall k, (k < 6)%nat -> val_mem tfibsegs (mrestrict (H W) (ms_mem ms)) (ap + 8 * Z.of_nat k) 8
  (bv_unsigned (getr regs (Z_to_bv 5 (12 + Z.of_nat k))))).
{ intros k Hk. replace (ap + 8 * Z.of_nat k) with (bv_unsigned (ew E0 2) + (-48 + 8 * Z.of_nat k)) by (rewrite E2; unfold ap, sp0; lia).
  apply (slot_of W E0 eA ms (- SP_STK) (- SP_STK) _ (SOff (Z.to_nat (12 + Z.of_nat k)) 0)).
  - exact HS.
  - vm_compute. reflexivity.
  - do 6 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
  - apply den_atom0'. rewrite (EOK_r regs E0 (12 + Z.of_nat k) HE ltac:(lia)). symmetry. apply Z_to_bv_bv_unsigned.
  - bvr. }
set (regsA := ms_regs ms) in *. set (memA := ms_mem ms) in *.
assert (SP : spZ regsA = sp0 - SP_FR).
{ unfold spZ at 1. subst regsA. rewrite (RG 2%bv (SOff 2 (- SP_FR))) by (vm_compute; reflexivity). cbn [sv_denot]. rewrite E2.
  rewrite unsigned_lit_small by zl. lia. }
assert (RA : getr regsA 1 = Z_to_bv 64 SP_RA_PCOM)
  by (subst regsA; rewrite (RG 1%bv (SLit SP_RA_PCOM)) by (vm_compute; reflexivity); reflexivity).
assert (A11 : getr regsA 11 = w64 f).
{ subst regsA. rewrite (RG 11%bv (SOff 11 0)) by (vm_compute; reflexivity). apply den_atom0'. rewrite (HE 11%nat 11%bv eq_refl). exact R11. }
assert (A12 : getr regsA 12 = w64 ap).
{ subst regsA. rewrite (RG 12%bv (SOff 2 (-48))) by (vm_compute; reflexivity). cbn [sv_denot]. rewrite E2. reflexivity. }
assert (A3 : getr regsA 3 = getr regs 3).
{ subst regsA. rewrite (RG 3%bv (SOff 3 0)) by (vm_compute; reflexivity). apply den_atom0'. exact (HE 3%nat 3%bv eq_refl). }
assert (A4 : getr regsA 4 = getr regs 4).
{ subst regsA. rewrite (RG 4%bv (SOff 4 0)) by (vm_compute; reflexivity). apply den_atom0'. exact (HE 4%nat 4%bv eq_refl). }
pose proof (ws0 memA md1 HI HV) as Hwords.
pose proof ws_len as WL.
pose proof HI as (HA1 & _ & Hp1 & _).
rewrite Hshape.
change (mkCfg (mkst regsA (Z_to_bv 64 (ss_pc eA)) memA (seg_rom tfibsegs)) md1) with (cfg_at tfibsegs SP_PCOM regsA memA md1).
eapply SRr_bind.
{ apply (APCOMMON ly S [] W regsA memA md1 f ap ws T).
  - apply ecall_preU_nil. apply (ecall0 memA md1 regsA HI);
      [rewrite RA; apply ret_ok_lit; [unfold SP_RA_PCOM; lia | reflexivity] | exact SP | exact A3 | exact A4].
  - rewrite SP. zl.
  - intros a Ha. rewrite SP in Ha. apply Hp1. zl.
  - exact A11.
  - exact A12.
  - exact (cv0 memA md1 HI).
  - exact Hcb.
  - apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) Hcd r Hr) as X.
    apply Forall_snp in X as [X1 _]. unfold zdisjoint in *. cbn [fst snd] in *. rewrite SP. zl.
  - exact Hwords.
  - rewrite WL, SP. unfold zdisjoint, ap. cbn [fst snd]. zl.
  - unfold ap. zl.
  - rewrite WL. unfold ap. zl.
  - apply (FR_cmd_mono _ (snp_out CMD_SP_K sp0 d w)); [exact (ff0 memA md1 HI)|].
    intros r' Hr'. destruct Hr' as [<-|[]]. exists (sp0 - CMD_SP_K, CMD_SP_K).
    split; [left; reflexivity | cbn [fst snd]; rewrite SP; zl]. }
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HA2 & Hap2 & Hsb2 & Hfr2 & Hpr2).
apply ARU_nil in HA2.
assert (RAZ : raZ regsA = SP_RA_PCOM) by (unfold raZ; rewrite RA; apply unsigned_lit_small; unfold SP_RA_PCOM; lia).
rewrite RAZ.
pose proof memB_ok as (MB1 & MB2 & MB3).
set (E1 := havoc E0 32 (map (getr regs2) CLOB)).
assert (HSB : st_ok tfibsegs E1 ssB (restrict (H W) (mkst regs2 (Z_to_bv 64 SP_RA_PCOM) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
  exact (st_ok_after_call tfibsegs 32 E0 eA _ regs2 (mrestrict (H W) mem2) memB SP_RA_PCOM HS
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) MB1 MB2 MB3 memB_sub
    ltac:(vm_compute; reflexivity) (regs_preserved_of_a regsA regs2 Hap2)
    ltac:(rewrite memB_shape;
          apply Forall_cons;
          [ apply (kept_stack W E0 memA mem2 sp0 (- SP_FR) (- SP_FR) _ E2); [zl | zl | lia | |];
            [ intros a Ha; apply Hfr2; [zl | rewrite SP; zl]
            | intros a Ha; apply Hpr2; apply Hp1; zl ]
          | apply Forall_forall; intros r Hr; apply (kept_ro W E0 memA mem2 r Hr); intros a Ha; apply Hfr2;
            [ lia | rewrite SP; zl ] ])). }
assert (HI2 : INV0 mem2 md2).
{ apply (fr_step B ly S W mem md _ _ (fun _ => False) memA md1 mem2 md2 HI HA2 Hsb2).
  - intros a Ha. apply Hpr2. apply Hp1. exact Ha.
  - intros a Ha H1 _. apply Hfr2; [exact Ha | rewrite SP; zl].
  - exact Hpr2. }
assert (HE1 : EOK regs E1) by (apply EOK_havoc; [exact HE | lia]).
assert (E2' : bv_unsigned (ew E1 2) = sp0) by (rewrite (HE1 2%nat 2%bv eq_refl); reflexivity).
pose proof winAB_ok as (_ & WB & _).
unfold cfg_at. change (w64 SP_RA_PCOM) with (Z_to_bv 64 SP_RA_PCOM).
eapply SRr_bind; [exact (spf_phase W E1 ssB eB _ (mkst regs2 (Z_to_bv 64 SP_RA_PCOM) mem2 (seg_rom tfibsegs)) md2 HSB r_B)|].
intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3).
change (st_ok tfibsegs E1 eB (restrict (H W) ms3)) in HS3.
apply (vsn_call E1 ms3 _ HS3 HE1).
exact (fr_runS B LAWS ly S W mem md sp0 (fun _ => False) mem2 md2 E1 ssB eB ms3 mat3 SP_FR L1 L2 ltac:(zl) ltac:(zl)
  ltac:(zl) HI2 E2' WB HF3 HS3 ltac:(vm_compute; reflexivity)).
Qed.

(* ---- the entry: run A ---- *)
Lemma spf_main : SRr tfibsegs W (cfg_at tfibsegs SP_ENTRY regs mem md) POST.
Proof using All.
pose proof basw as (B1 & B2 & B3 & L1 & L2 & _).
pose proof HPRE as (HA & _).
set (E0 := Ereg regs []).
assert (HE0 : EOK regs E0) by (apply EOK_Ereg).
assert (E2 : bv_unsigned (ew E0 2) = sp0) by (rewrite (HE0 2%nat 2%bv eq_refl); reflexivity).
assert (RO : Forall (region_ok tfibsegs E0 (mrestrict (H W) mem)) (map ro_region spf_rodata))
  by exact (rodata_ok B TB spf_rodata ly S (H W) mem E0 (spf_rodata_chk ly) (proj1 HA)).
assert (HS0 : st_ok tfibsegs E0 ssA (restrict (H W) (mkst regs (Z_to_bv 64 SP_ENTRY) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssA. apply (entry_st_ok_full tfibsegs); change (Ereg regs []) with E0.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|exact RO].
    unfold stkA. apply (region_ok_stack tfibsegs E0 _ 2 sp0 (- SP_STK)); [exact E2 | zl | zl |].
    intros a Ha. apply apresent_writable. apply HKp. zl.
  - apply pairwise_disjoint_of_extents. unfold stkA, spf_rodata, icpt_rodata, ro_region, extent_of_region.
    cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; zl.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok factsA]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
    change (2 ^ 4) with 16. split; [|exact I]. split; [zl|]. split; [exact B3 | lia]. }
unfold cfg_at. change (w64 SP_ENTRY) with (Z_to_bv 64 SP_ENTRY).
eapply SRr_bind; [exact (spf_phase W E0 ssA eA _ _ md HS0 r_A)|].
intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1).
change (st_ok tfibsegs E0 eA (restrict (H W) ms1)) in HS1.
pose proof winAB_ok as (WA & _).
apply (pcom_call E0 ms1 _ HS1 HE0).
exact (fr_runS B LAWS ly S W mem md sp0 (fun _ => False) mem md E0 ssA eA ms1 mat1 SP_STK L1 L2 ltac:(zl) ltac:(zl)
  ltac:(zl) (fr_init B ly S W mem md (sp0 - spK) sp0 (fun _ => False) HA (fun a Ha => HKp a Ha)) E2 WA HF1 HS1
  ltac:(vm_compute; reflexivity)).
Qed.
End w.

(* sprintf at its trampoline 0x45180: our sprintf text at fuzz_command's family FR_cmd; the walk's consts_view over
   CMD_SP_CR comes from the contract's rt_rom_view and AR (RtPFCv.cmd_cr_consts_view) *)
Theorem spf_walk : sh_asprintf_realizes tfibsegs B FR_cmd CMD_SP_K CMD_GOTW CMD_GUARD CMD_IMG_LO CMD_IMG_HI CMD_SP_CR SP_ENTRY.
Proof.
intros ly S W regs mem md d f xs ws T cval HPRE HKlo HKp R10 R11 Hrom Hcb Hcd Hgc Hgv G1 G2 G3 G4 Hgcd Hgvd Hva Hxs Hxsd
  HFF HT Hd0 Hdw Hpw Hdst Ham Hra Hhull Hdog Hfrm H47 Hd8.
exact (spf_main ly S W regs mem md d f xs ws T cval HPRE HKlo HKp R10 R11
  (RtPFCv.cmd_cr_consts_view B TB ly S W regs mem md HPRE Hrom) Hcb Hcd Hgc Hgv Hgcd Hgvd Hva Hxs Hxsd
  HFF HT Hd0 Hdw Hpw Hdst Ham Hra Hhull Hdog Hfrm H47 Hd8).
Qed.
End b.
