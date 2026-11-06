(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import SumWalkTac Frame.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc Require Import RelocKit .
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl Require Import MuslTac MemcpyBase Memchr Strnlen.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import PFLib.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc Require Import RelocKit .
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl Require Import MuslTac PFBase.
Import ListNotations.
Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section GD_1.
  Context {RL : Reloc}.
Definition flatZ (a len : Z) : Prop := 0 <= a /\ 0 <= len /\ a + len <= 2 ^ 64.
End GD_1.
Section GD_2.
  Context {RL : Reloc}.
Definition rostr_win (a k : Z) : Z := ((a + k) / 8) * 8 + 8 - a.
End GD_2.
Section GD_3.
  Context {RL : Reloc}.
Definition rostr (M : word -> option byte) (a k : Z) : Prop :=
  0 <= k /\ flatZ a (rostr_win a k)
  /\ (forall i, 0 <= i <= k -> M (Z_to_bv 64 (a + i)) = None)
  /\ (forall i, 0 <= i < k -> exists b : byte, seg_rom SEGS (Z_to_bv 64 (a + i)) = Some b /\ bv_unsigned b <> 0)
  /\ seg_rom SEGS (Z_to_bv 64 (a + k)) = Some (Z_to_bv 8 0)
  /\ (exists bs, rdn SEGS M (Z_to_bv 64 a) (Z.to_nat (rostr_win a k)) = Some bs).
End GD_3.

Section STR.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
  Variables (sp0 : Z) (mem0 : word -> option byte) (cv : Z) (rom : word -> option byte).
  Hypothesis CTX : ctxH sp0 mem0 cv.
  Variables (a k : Z).
  Hypothesis RS : rostr mem0 a k.
  Hypothesis Hk : k <= 200.

  Let Hcsp : IMG_TOP + FR <= sp0 <= 0x800000000000 := Csp _ _ _ CTX.

  Lemma rostr_win_ge : k + 1 <= rostr_win a k /\ rostr_win a k <= k + 8.
  Proof.
    destruct RS as (K0 & (A0 & _) & _). unfold rostr_win.
    pose proof (Z.div_mod (a + k) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (a+k) 8 ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rostr_range : rl_img_lo <= a /\ a + k < rl_img_hi /\ a + rostr_win a k <= rl_img_hi.
  Proof.
    destruct RS as (K0 & FL & NONE & NZ & ZE & _).
    destruct FL as (A0 & W0 & AW). lay.
    assert (R0 : IMG_LO <= a + k < IMG_TOP).
    { pose proof (rom_range _ _ ZE) as R. unfold rostr_win in AW.
      pose proof (Z.div_mod (a + k) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (a+k) 8 ltac:(lia)).
      rewrite u_Z2bv in R; lia. }
    unfold IMG_LO, IMG_TOP in R0.
    assert (R1 : rl_img_lo <= a).
    { destruct (Z.eq_dec k 0) as [->|Kp]; [lia|].
      destruct (NZ 0 ltac:(lia)) as (b & E & _).
      pose proof (rom_range _ _ E) as R. unfold IMG_LO, IMG_TOP in R. rewrite u_Z2bv in R by lia. lia. }
    unfold IMG_LO, IMG_TOP in *.
    split; [exact R1|]. split; [lia|].
    unfold rostr_win. pose proof (Z.div_mod (a + k) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (a+k) 8 ltac:(lia)).
    pose proof (Z.div_mod rl_img_hi 8 ltac:(lia)) as HM. rewrite rl_img_hi_mod8 in HM.   (* [comment removed for export] *)
    set (x := (a + k) / 8) in *. set (y := rl_img_hi / 8) in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mchrH_rostr : forall m, FRM sp0 mem0 m ->
    exists buf, length buf = Z.to_nat (rostr_win a k) /\ mchrH m (Z_to_bv 64 a) buf k 0x7fffffff.
  Proof.
    intros m F. pose proof Hcsp as Hsp0. lay.
    pose proof rostr_range as RR. pose proof rostr_win_ge as WG. lay.
    destruct RS as (K0 & FL & NONE & NZ & ZE & [bs Hbs]).
    pose proof (rdn_length _ _ _ _ _ Hbs) as L.
    assert (Hbs' : rdn SEGS m (Z_to_bv 64 a) (Z.to_nat (rostr_win a k)) = Some bs).
    { rewrite (FRM_rdn sp0 mem0 cv CTX m a _ F); [exact Hbs | lia | lay; lia | lia]. }
    (* [comment removed for export] *)
    assert (BY : forall i, 0 <= i <= k -> exists b, seg_rom SEGS (Z_to_bv 64 (a + i)) = Some b
                         /\ nth (Z.to_nat i) bs (Z_to_bv 8 0) = b).
    { intros i Hi.
      pose proof (rdn_nth SEGS mem0 _ (Z_to_bv 64 a) bs (Z.to_nat i) Hbs ltac:(lia)) as B.
      replace (Z_to_bv 64 a + nat_to_word (Z.to_nat i))%bv with (Z_to_bv 64 (a + i)) in B.
      2:{ unfold nat_to_word. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
          unfold bv_wrap. rewrite <- Zplus_mod. f_equal. lia. }
      cbn [rdn] in B. rewrite (NONE i Hi) in B.
      destruct (seg_rom SEGS (Z_to_bv 64 (a + i))) as [b|] eqn:E; [|discriminate B].
      exists b. split; [reflexivity|]. injection B as B'. symmetry. exact B'. }
    exists bs. split; [exact L|].
    unfold rostr_win in *. set (x := (a + k) / 8) in *.
    pose proof (Z.div_mod (a + k) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (a+k) 8 ltac:(lia)) as MB.
    fold x in DM.
    split.
    - rewrite L. exact Hbs'.
    - rewrite L. unorm. lia.
    - rewrite L. unorm. lia.
    - lia.
    - destruct (BY k ltac:(lia)) as (b & E & N). rewrite N. rewrite ZE in E. injection E as <-. reflexivity.
    - intros j Hj. destruct (BY (Z.of_nat j) ltac:(lia)) as (b & E & N).
      rewrite Nat2Z.id in N. rewrite N.
      destruct (NZ (Z.of_nat j) ltac:(lia)) as (b' & E' & NZ'). rewrite E' in E. injection E as ->. exact NZ'.
    - lia.
    - lia.
    - split; intros i Hi; (apply (FRM_none sp0 mem0 cv CTX m i F); lay; lia).
  Qed.

  (* [comment removed for export] *)
  Lemma strnlen_rostr : forall m (sp : Z) regs (ret : word),
    FRM sp0 mem0 m -> sp0 - FR + 32 <= sp <= sp0 ->
    ret_ok ret -> getr regs 1 = ret -> getr regs 2 = Z_to_bv 64 sp ->
    getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 0x7fffffff ->
    exists r m',
      msteps SEGS (mkst regs (rl dF_1cf40 0x1cf40) m rom) (mkst r ret m' rom)
      /\ (keeps_cs regs r /\ getr r 10 = Z_to_bv 64 k
          /\ frame_mod m m' [(Z_to_bv 64 (sp - 32), 32)]).
  Proof.
    intros m sp regs ret F Hsp Hret H1 H2 H10 H11. pose proof Hcsp as Hsp0. lay.
    pose proof rostr_range as RR. pose proof rostr_win_ge as WG. lay.
    assert (K0 : 0 <= k) by (destruct RS as [K0 _]; exact K0).
    destruct (mchrH_rostr m F) as (buf & L & MH).
    destruct (ref_strnlen m (Z_to_bv 64 a) (Z_to_bv 64 sp) buf k 0x7fffffff rom regs ret MH)
      as (r & m' & RUN & K & A10 & FM); try assumption.
    - unorm. lia.
    - unorm. eapply (FRM_sok sp0 mem0 cv CTX); [exact F | lay; lia | lay; lia].
    - unorm. lia.
    - left. rewrite L. unorm. lia.
    - exists r, m'. split; [exact RUN|]. split; [exact K|]. split; [exact A10|].
      revert FM. unorm. intros FM. exact FM.
  Qed.
End STR.
