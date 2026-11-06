(* fm's snprintf glue, transport: the chain's premises (gl_pre, vsn_file, snk_base) after a step of a walk that changes
   only the band and the destination's first byte, ecall_preU from ARU, and the shadow facts of a stack range or a prefix
   of the destination. New file. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC20 YI00 YI16 YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE20 AE2y AE3h.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMsnprintfI FMsnprintfK.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMsnprintfGI FMsnprintfGk.
Import ListNotations.
Open Scope Z_scope.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
#[local] Abbreviation H W := (w_H W).

Lemma ac_bounds : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
Proof. exact (proj1 alloc_ceiling_val). Qed.
(* the image's first read-only segment [0x10000, 0x30000) *)
Lemma rom_seg0 : forall a, 0x10000 <= a < 0x30000 -> in_rom tfibsegs a.
Proof.
intros a Ha. unfold in_rom.
assert (P : nth_error (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) tfibsegs) 0 =
  Some (65536, 131072, false)) by (vm_compute; reflexivity).
destruct tfibsegs as [|s1 rest]; [discriminate|].
cbn [map nth_error] in P. injection P as P1 P2 P3.
exists s1. split; [left; reflexivity|]. split; [exact P3|]. lia.
Qed.
Lemma fmt_place : forall f ps, In (f, ps) FM_SN_FMTS ->
  0x20000 <= f /\ f + Z.of_nat (length (fmt_bytes ps)) + 8 <= 0x21000.
Proof.
intros f ps Hin. unfold FM_SN_FMTS in Hin.
repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; cbn [fmt_bytes length app];
  unfold FMT_whole, FMT_tw, FMT_tx, FMT_t1, FMT_t2, FMT_t3, FMT_t1x; lia|]).
destruct Hin.
Qed.
(* a byte the world may hide stays writable when its presence is kept *)
Lemma writable_xfer : forall (Hd : word -> bool) (m m' : word -> option byte) a,
  writable_at tfibsegs (mrestrict Hd m) a -> (apresent Hd m a -> apresent Hd m' a) ->
  writable_at tfibsegs (mrestrict Hd m') a.
Proof.
intros Hd m m' a Hw Hp. unfold writable_at, wview, mrestrict in *.
destruct (Hd (Z_to_bv 64 a)) eqn:Eh; [exact Hw|].
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
- destruct (Hp (conj Eh (ex_intro _ b Em))) as [_ [b' Hb']]. rewrite Hb'. discriminate.
- destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.

(* ---- a step that keeps every byte outside the stack below TOPK (>= the band's top) and the destination's first
   byte ---- *)
Section x.
Variables (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (mem : word -> option byte) (md : Model)
  (mem' : word -> option byte) (md' : Model) (sp0 D TOPK : Z).
Hypothesis Hbase : snk_base B ly S U W mem md sp0.
Hypothesis HD : 0 < D /\ amem_range D 1 /\ ~ in_rom tfibsegs D.
Hypothesis KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - SNK_STK <= a < TOPK) -> a <> D ->
  aview tfibsegs (H W) mem' a = aview tfibsegs (H W) mem a.
Hypothesis DV : aview tfibsegs (H W) mem' D = aview tfibsegs (H W) mem D \/ aview tfibsegs (H W) mem' D = Some 0.
Lemma x_layout : alloc_ceiling <= sp0 - SNK_STK /\ kHighMemBeg <= sp0 - SNK_STK /\ sp0 + 0x200 <= 2 ^ 47 /\
  sp0 mod 16 = 0.
Proof. destruct Hbase as (_ & Hac & _ & H16 & Hlo & _ & H47 & Hkh & _). lia. Qed.
(* the shadow lies below the stack and away from the destination *)
Lemma x_shadow : forall s, SHADOW_OFF <= s < kHighMemBeg -> aview tfibsegs (H W) mem' s = aview tfibsegs (H W) mem s.
Proof.
intros s Hs. pose proof x_layout as (L1 & L2 & L3 & L4). destruct HD as (_ & Ham & _).
apply KEEP; [unfold SHADOW_OFF, kHighMemBeg in *; lia | lia |].
intros ->. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia.
Qed.
Lemma x_tail : forall a, 0 <= a < alloc_ceiling -> aview tfibsegs (H W) mem a <> None -> aview tfibsegs (H W) mem' a <> None.
Proof.
intros a Ha Hv. pose proof x_layout as (L1 & L2 & L3 & L4). pose proof ac_bounds as ACB.
destruct (Z.eq_dec a D) as [->|Hne].
- destruct DV as [E|E]; rewrite E; [exact Hv | discriminate].
- rewrite KEEP by lia. exact Hv.
Qed.
(* a C string below alloc_ceiling whose bytes and NUL miss D *)
Lemma cstr_ok_x : forall p l, cstr_ok tfibsegs W mem p l ->
  (forall a, p <= a < p + Z.of_nat (length l) + 1 -> a <> D) -> cstr_ok tfibsegs W mem' p l.
Proof.
intros p l ((Hg & Hnz) & H4 & Hac & H32 & Ham & Hra & Hhull & Htail) HnD.
pose proof x_layout as (L1 & L2 & L3 & L4). pose proof ac_bounds as ACB.
assert (KS : forall a, p <= a < p + Z.of_nat (length l) + 1 -> aview tfibsegs (H W) mem' a = aview tfibsegs (H W) mem a).
{ intros a Ha. apply KEEP; [lia | lia | apply HnD; exact Ha]. }
split; [split; [|exact Hnz]|].
- intros j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
  apply (val_mem_kept (H W) (H W) mem mem'); [|exact Hv].
  intros k Hk. rewrite length_app in Hj. cbn [length] in Hj. apply KS. lia.
- split; [exact H4|]. split; [exact Hac|]. split; [exact H32|]. split; [exact Ham|]. split; [|split].
  + intros x Hx. destruct (Hra x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
    rewrite x_shadow; [exact Hs|]. unfold shadow_of_addr, SHADOW_OFF, kHighMemBeg.
    pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono x (2 ^ 47) 8 ltac:(lia) ltac:(lia)). lia.
  + intros s Hs. rewrite x_shadow; [exact (Hhull s Hs)|]. unfold shadow_addr, SHADOW_OFF, kHighMemBeg in *.
    pose proof (Z.div_pos p 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (p + Z.of_nat (length l) + 1 - 1) (2 ^ 47) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_mod (2147450880 + p / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (2147450880 + p / 8) 8 ltac:(lia)).
    pose proof (Z.div_mod (2147450880 + (p + Z.of_nat (length l) + 1 - 1) / 8) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (2147450880 + (p + Z.of_nat (length l) + 1 - 1) / 8) 8 ltac:(lia)).
    lia.
  + intros a Ha. apply x_tail; [|exact (Htail a Ha)].
    pose proof (Z.mod_pos_bound (p + Z.of_nat (length l)) 8 ltac:(lia)). lia.
Qed.
Lemma frender_x : forall N ps args out, 1 <= N -> frender tfibsegs W mem D N ps args out -> frender tfibsegs W mem' D N ps args out.
Proof.
intros N ps. induction ps as [|pc ps IH]; intros args out HN Hf; [exact Hf|].
destruct pc as [l| |]; cbn [frender] in Hf |- *.
- destruct Hf as (out' & -> & Hf). exists out'. split; [reflexivity | exact (IH args out' HN Hf)].
- destruct args as [|p args]; [exact Hf|]. destruct Hf as (s & out' & Hc & Hdj & -> & Hf).
  exists s, out'. split; [|split; [exact Hdj | split; [reflexivity | exact (IH args out' HN Hf)]]].
  apply (cstr_ok_x p s Hc). intros a Ha ->. lia.
- destruct args as [|k [|p args]]; try exact Hf. destruct Hf as (s & out' & Hk & Hc & Hdj & -> & Hf).
  exists s, out'. split; [exact Hk|]. split; [|split; [exact Hdj | split; [reflexivity | exact (IH args out' HN Hf)]]].
  apply (cstr_ok_x p s Hc). intros a Ha ->. lia.
Qed.
End x.

(* gl_pre at mem' from its parts at mem, after a step that changes only the stack below TOPK (>= the band's top) and
   possibly D's first byte (to 0); the slots are given at mem' *)
Lemma gl_pre_mk : forall ly S U W mem md mem' md' sp0 D N M f ps P args out TOPK,
  snk_base B ly S U W mem md sp0 -> rom_viewN tfibsegs B W mem ->
  (exists cval, val_mem tfibsegs (mrestrict (H W) mem) FM_GOT_canary 8 FM_canary /\
     val_mem tfibsegs (mrestrict (H W) mem) FM_canary 8 cval /\ 0 <= cval < 2 ^ 64) ->
  In (f, ps) FM_SN_FMTS -> cstr_ok tfibsegs W mem f (fmt_bytes ps) ->
  sp0 + 0x200 <= P -> P + 8 * Z.of_nat (length args) <= ly_stk_hi ly ->
  frender tfibsegs W mem D N ps args out -> Z.of_nat (length out) + 1 <= M <= N -> N <= 2 ^ 30 ->
  snk_dest B ly S W mem D M -> sp0 + 0x200 <= TOPK ->
  ARU tfibsegs B ly S U W mem' md' ->
  (forall a, snk_band sp0 a -> apresent (H W) mem' a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - SNK_STK <= a < TOPK) -> a <> D ->
     aview tfibsegs (H W) mem' a = aview tfibsegs (H W) mem a) ->
  (aview tfibsegs (H W) mem' D = aview tfibsegs (H W) mem D \/ aview tfibsegs (H W) mem' D = Some 0) ->
  (forall a, apresent (H W) mem a -> apresent (H W) mem' a) ->
  slots_at W mem' P args ->
  gl_pre B ly S U W mem' md' sp0 D N M f ps P args out.
Proof.
intros ly S U W mem md mem' md' sp0 D N M f ps P args out TOPK
  Hbase Hrom (cval & Hgot & Hcan & Hcv) Hin Hfc HP1 HP2 Hfr HM HN Hdst HTOP HA' BAND' KEEP DV PRES Hsl.
pose proof Hbase as (HA & Hac & H44 & H16 & Hlo & Hhi & H47 & Hkh & Hband & Hzs).
pose proof Hdst as (HD0 & HDhi & HM30 & HDcan & HDw & HDam & HDra & HDhull).
pose proof ac_bounds as ACB.
pose proof (stk_kHighMemBeg B ly S _ (ARU_ARm tfibsegs B ly S U W mem md HA)) as [K1 K2].
assert (HDrom : ~ in_rom tfibsegs D) by (destruct (HDw D ltac:(lia)) as (_ & _ & X); exact X).
assert (HD : 0 < D /\ amem_range D 1 /\ ~ in_rom tfibsegs D).
{ split; [exact HD0|]. split; [unfold amem_range in *; lia | exact HDrom]. }
pose proof (x_layout ly S U W mem md sp0 Hbase) as (L1 & L2 & L3 & L4).
assert (KS := x_shadow ly S U W mem md mem' sp0 D TOPK Hbase HD KEEP).
assert (KL : forall a, 0 <= a < alloc_ceiling -> a <> D -> aview tfibsegs (H W) mem' a = aview tfibsegs (H W) mem a).
{ intros a Ha Hne. apply KEEP; [lia | lia | exact Hne]. }
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]].
- (* snk_base *)
  split; [exact HA'|]. do 7 (split; [assumption|]). split; [exact BAND'|].
  intros i Hi. rewrite KS; [exact (Hzs i Hi)|]. unfold shadow_of_addr, SHADOW_OFF, kHighMemBeg in *.
  assert (HSS0 : SNK_STK = 9104) by reflexivity.
  pose proof (Z.div_le_mono (sp0 - SNK_STK) (2 ^ 47) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos (sp0 - SNK_STK) 8 ltac:(lia) ltac:(lia)).
  assert (HSS1 : (SNK_STK + 0x200) / 8 = 1202) by reflexivity. lia.
- (* rom_viewN *)
  intros a Ha Hno Hne. pose proof (tfib_rom_low a Ha) as Hl. rewrite KEEP; [exact (Hrom a Ha Hno Hne) | lia | lia |].
  intros ->. exact (HDrom Ha).
- (* canary cells *)
  exists cval. split; [|split; [|exact Hcv]].
  + assert (RC : rodata_chk ly [(FM_GOT_canary, 8, [(0, 8%N, FM_canary)])] = true).
    { unfold FM_GOT_canary, FM_canary. vm_compute. reflexivity. }
    pose proof (rodata_ok B TB _ ly S (H W) (unpoison U mem') (mkEnv (fun _ => Z_to_bv 64 0) (fun _ => [])) RC
      (ARU_ARm tfibsegs B ly S U W mem' md' HA')) as HR.
    apply Forall_inv in HR. unfold ro_region in HR. cbn [fst snd map ro_chunk] in HR.
    destruct HR as (_ & _ & _ & HC). apply Forall_inv in HC.
    pose proof (val_of_chunk_ok tfibsegs _ _ _ _ 8%N (SLit FM_canary) FM_canary HC eq_refl
      ltac:(unfold FM_canary; lia) ltac:(lia)) as Hv.
    rewrite Z.add_0_r in Hv. cbn [N.to_nat] in Hv.
    apply (val_mem_ext (mrestrict (H W) (unpoison U mem'))); [|exact Hv].
    intros k Hk. unfold mbyte, mrestrict. rewrite (ARU_mem_low tfibsegs B ly S U W mem' md' _ HA'); [reflexivity|].
    rewrite unsigned_lit_small; unfold FM_GOT_canary, SHADOW_OFF; lia.
  + apply (val_mem_kept (H W) (H W) mem mem'); [|exact Hcan].
    intros k Hk. apply KL; [unfold FM_canary in *; lia|]. intros E. unfold FM_canary in *. lia.
- exact Hin.
- (* the format *)
  pose proof (fmt_place f ps Hin) as Fp.
  apply (cstr_ok_x ly S U W mem md mem' sp0 D TOPK Hbase HD KEEP DV f _ Hfc).
  intros a Ha ->. apply HDrom. apply rom_seg0. lia.
- exact HP1.
- exact HP2.
- exact Hsl.
- exact (frender_x ly S U W mem md mem' sp0 D TOPK Hbase HD KEEP DV N ps args out ltac:(lia) Hfr).
- exact HM.
- exact HN.
- (* the destination *)
  split; [exact HD0|]. split; [exact HDhi|]. split; [exact HM30|]. split; [exact HDcan|].
  split; [|split; [exact HDam|split]].
  + intros a Ha. destruct (HDw a Ha) as (Hw & Ho & Hr). split; [|split; [exact Ho | exact Hr]].
    exact (writable_xfer (H W) mem mem' a Hw (PRES a)).
  + intros x Hx. destruct (HDra x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
    rewrite KS; [exact Hs|]. unfold shadow_of_addr, SHADOW_OFF, kHighMemBeg, amem_range, kLowMemEnd, kHighMemEnd in *.
    pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono x (2 ^ 47) 8 ltac:(lia) ltac:(lia)). lia.
  + intros s Hs. rewrite KS; [exact (HDhull s Hs)|]. unfold shadow_addr, SHADOW_OFF, kHighMemBeg, amem_range, kLowMemEnd, kHighMemEnd in *.
    pose proof (Z.div_pos D 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (D + M - 1) (2 ^ 47) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_mod (2147450880 + D / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (2147450880 + D / 8) 8 ltac:(lia)).
    pose proof (Z.div_mod (2147450880 + (D + M - 1) / 8) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (2147450880 + (D + M - 1) / 8) 8 ltac:(lia)).
    lia.
Qed.
(* gl_pre after a step that changes only the stack below P (the band and the frames above it) and possibly D's first
   byte (to 0) *)
Lemma gl_pre_xfer : forall ly S U W mem md mem' md' sp0 D N M f ps P args out,
  gl_pre B ly S U W mem md sp0 D N M f ps P args out ->
  ARU tfibsegs B ly S U W mem' md' ->
  (forall a, snk_band sp0 a -> apresent (H W) mem' a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - SNK_STK <= a < P) -> a <> D ->
     aview tfibsegs (H W) mem' a = aview tfibsegs (H W) mem a) ->
  (aview tfibsegs (H W) mem' D = aview tfibsegs (H W) mem D \/ aview tfibsegs (H W) mem' D = Some 0) ->
  (forall a, apresent (H W) mem a -> apresent (H W) mem' a) ->
  gl_pre B ly S U W mem' md' sp0 D N M f ps P args out.
Proof.
intros ly S U W mem md mem' md' sp0 D N M f ps P args out
  (Hbase & Hrom & Hcan & Hin & Hfc & HP1 & HP2 & Hsl & Hfr & HM & HN & Hdst) HA' BAND' KEEP DV PRES.
apply (gl_pre_mk ly S U W mem md mem' md' sp0 D N M f ps P args out P); try assumption.
pose proof Hbase as (HA & Hac & H44 & H16 & Hlo & Hhi & H47 & Hkh & _).
pose proof Hdst as (HD0 & HDhi & _ & _ & _ & _ & _ & _).
pose proof (stk_kHighMemBeg B ly S _ (ARU_ARm tfibsegs B ly S U W mem md HA)) as [K1 K2].
pose proof ac_bounds as ACB.
intros i Hi. apply (val_mem_kept (H W) (H W) mem mem'); [|exact (Hsl i Hi)].
intros k Hk. assert (KE : kHighMemEnd = 2 ^ 47) by reflexivity. assert (HSS : SNK_STK = 9104) by reflexivity.
apply KEEP.
* nia.
* intros [Hq1 Hq2]. nia.
* intros Hq. nia.
Qed.

(* the FILE and its cookie as vsnprintf left them *)
Lemma vsn_file_xfer : forall W mem mem' sp0 D N,
  vsn_file W mem sp0 D N ->
  (forall a, sp0 + FO <= a < sp0 + CKO + 16 -> aview tfibsegs (H W) mem' a = aview tfibsegs (H W) mem a) ->
  aview tfibsegs (H W) mem' D = aview tfibsegs (H W) mem D ->
  vsn_file W mem' sp0 D N.
Proof.
intros W mem mem' sp0 D N [HF HD] Hk HDk. split; [|rewrite HDk; exact HD].
rewrite Forall_forall in HF |- *. intros c Hc. pose proof (HF c Hc) as Hv.
apply (val_mem_kept (H W) (H W) mem mem'); [|exact Hv].
intros k Hk'. apply Hk. unfold vsn_fields in Hc. unfold CKO, FO.
repeat (destruct Hc as [Hc|Hc]; [subst c; cbn [fst snd] in *; lia|]). destruct Hc.
Qed.

(* snk_base at the memory a walk reached under its frame *)
Lemma snk_base_frame : forall ly S U W mem0 md0 sp0 top XW mem md,
  snk_base B ly S U W mem0 md0 sp0 -> snk_frame B ly S U W mem0 md0 sp0 top XW mem md -> top <= sp0 + 0x200 ->
  (forall a, XW a -> a < SHADOW_OFF \/ kHighMemBeg <= a) -> snk_base B ly S U W mem md sp0.
Proof.
intros ly S U W mem0 md0 sp0 top XW mem md Hb (HA & _ & Hp & Hfr & _) Ht HX.
destruct Hb as (_ & Hac & H44 & H16 & Hlo & Hhi & H47 & Hkh & _ & Hzs).
split; [exact HA|]. do 7 (split; [assumption|]). split; [exact Hp|].
intros i Hi. assert (HSS0 : SNK_STK = 9104) by reflexivity. assert (HSS1 : (SNK_STK + 0x200) / 8 = 1202) by reflexivity.
pose proof (Z.div_le_mono (sp0 - SNK_STK) (2 ^ 47) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_pos (sp0 - SNK_STK) 8 ltac:(lia) ltac:(lia)).
rewrite Hfr; [exact (Hzs i Hi) | unfold shadow_of_addr, SHADOW_OFF in *; lia | unfold shadow_of_addr, SHADOW_OFF, kHighMemBeg in *; lia |].
intros Hx. destruct (HX _ Hx) as [Y|Y]; unfold shadow_of_addr, SHADOW_OFF, kHighMemBeg in *; lia.
Qed.

(* ecall_preU from ARU, the registers and the ESTACK window *)
Lemma g_ecall_preU : forall ly S U W regs mem md,
  ARU tfibsegs B ly S U W mem md -> YK0s.ret_ok (getr regs 1) -> spZ regs mod 16 = 0 ->
  ly_stk_lo ly + ESTACK <= spZ regs -> spZ regs <= ly_stk_hi ly ->
  (forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (H W) mem a) ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  ecall_preU tfibsegs B ly S U W regs mem md.
Proof.
intros ly S U W regs mem md HA Hra H16 Hlo Hhi Hp Hgp Htp.
pose proof (stk_kHighMemBeg B ly S _ (ARU_ARm tfibsegs B ly S U W mem md HA)) as [K1 K2].
split; [|split; [exact (ARU_ok tfibsegs B ly S U W mem md HA) | exact (ARU_poisoned tfibsegs B ly S U W mem md HA)]].
split; [exact (ARU_AR tfibsegs B ly S U W mem md HA)|]. do 4 (split; [assumption|]). split; [|split; assumption].
intros a Ha. destruct (Hp a Ha) as [Hh [b Hb]]. split; [exact Hh|]. exists b.
unfold ESTACK in *.
rewrite unpoison_out; [exact Hb|]. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Ei; [|reflexivity].
exfalso. pose proof (ush_facts tfibsegs B ly S U W mem md _ HA Ei) as (_ & L1 & L2).
rewrite unsigned_lit_small in L2 by (unfold kHighMemEnd, kHighMemBeg in *; lia). lia.
Qed.

(* the shadow facts of a stack range well inside the band *)
Lemma band_addressable : forall ly S U W mem md sp0 x n,
  snk_base B ly S U W mem md sp0 -> sp0 - SNK_STK + 64 <= x -> x + n + 64 <= sp0 + 0x200 -> x mod 8 = 0 -> n mod 8 = 0 ->
  range_addressable (aview tfibsegs (H W) mem) SHADOW_OFF x n /\
  (0 < n -> shadow_hull_vis (aview tfibsegs (H W) mem) x n).
Proof.
intros ly S U W mem md sp0 x n Hb Hx1 Hx2 Hx8 Hn8.
destruct Hb as (_ & Hac & H44 & H16 & Hlo & Hhi & H47 & Hkh & _ & Hzs).
assert (HSS0 : SNK_STK = 9104) by reflexivity. assert (HSS1 : (SNK_STK + 0x200) / 8 = 1202) by reflexivity.
assert (Hsp : sp0 = 16 * (sp0 / 16)) by (pose proof (Z.div_mod sp0 16 ltac:(lia)); lia).
assert (Hxq : x = 8 * (x / 8)) by (pose proof (Z.div_mod x 8 ltac:(lia)); lia).
assert (Hnq : n = 8 * (n / 8)) by (pose proof (Z.div_mod n 8 ltac:(lia)); lia).
assert (Hb8 : (sp0 - SNK_STK) / 8 = 2 * (sp0 / 16) - 1138).
{ rewrite Hsp at 1. replace (16 * (sp0 / 16) - SNK_STK) with ((2 * (sp0 / 16) - 1138) * 8) by lia. apply Z.div_mul. lia. }
assert (Z0 : forall s, SHADOW_OFF + (sp0 - SNK_STK) / 8 <= s < SHADOW_OFF + (sp0 - SNK_STK) / 8 + 1202 ->
  aview tfibsegs (H W) mem s = Some 0).
{ intros s Hs. replace s with (shadow_of_addr SHADOW_OFF (sp0 - SNK_STK) + (s - SHADOW_OFF - (sp0 - SNK_STK) / 8))
    by (unfold shadow_of_addr; lia). apply Hzs. lia. }
split.
- apply zero_shadow_range; [exact Hx8 | exact Hn8|]. intros i Hi. apply Z0. unfold shadow_of_addr. lia.
- intros Hn s Hs. rewrite Z0; [discriminate|]. unfold shadow_addr, SHADOW_OFF in *. lia.
Qed.

(* the destination's facts for a prefix of it *)
Lemma dest_sub : forall ly S W mem D M n,
  snk_dest B ly S W mem D M -> 1 <= n <= M ->
  amem_range D n /\ range_addressable (aview tfibsegs (H W) mem) SHADOW_OFF D n /\
  shadow_hull_vis (aview tfibsegs (H W) mem) D n.
Proof.
intros ly S W mem D M n (HD0 & HDhi & HM & _ & _ & Ham & Hra & Hhull) Hn.
split; [unfold amem_range in *; lia|]. split.
- intros x Hx. apply Hra. lia.
- intros s Hs. apply Hhull. unfold shadow_addr in *.
  pose proof (Z.div_le_mono (D + n - 1) (D + M - 1) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono (SHADOW_OFF + (D + n - 1) / 8) (SHADOW_OFF + (D + M - 1) / 8) 8 ltac:(lia) ltac:(lia)).
  lia.
Qed.
End t.
