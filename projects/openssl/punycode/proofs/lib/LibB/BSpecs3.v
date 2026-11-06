(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import FpLift WpEngine LibKit StrKit WpTac WpMem.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import AShadow.
From OSSVerify.Proofs.openssl.punycode.lib.LibB Require Import BCode BRt BImg BRtIc BIface BInit BRtInst.
From OSSVerify.Proofs.openssl.punycode.lib.LibB Require BFakeStack.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma rget_lof : forall regs (k : nat), (0 < k < 32)%nat -> rget (lof regs) k = getr regs (Z_to_bv 5 (Z.of_nat k)).
Proof. intros regs k Hk. symmetry. apply rrel_getr; [apply rrel_lof | exact Hk]. Qed.

Ltac lof_reg :=
  rewrite rget_lof by lia;
  match goal with |- getr _ (Z_to_bv 5 (Z.of_nat ?k)) = _ =>
    let r := eval cbv in (Z.of_nat k) in
    replace (Z_to_bv 5 (Z.of_nat k)) with (Z_to_bv 5 r) by reflexivity end;
  match goal with H : getr _ ?r = ?v |- getr _ ?r' = ?v =>
    replace r' with r by (apply bv_eq; reflexivity); exact H end.

(* [comment removed for export] *)
Ltac reg_out HRR Hv :=
  match goal with |- getr ?regs' ?r = _ =>
    let k := eval cbv in (Z.to_nat (bv_unsigned r)) in
    replace r with (Z_to_bv 5 (Z.of_nat k)) by (apply bv_eq; reflexivity);
    rewrite (rrel_getr regs' _ k HRR) by lia; exact Hv end.

(* [comment removed for export] *)
Theorem wpinit_r1_spec : forall regs F fc M rom fs T ctx thr h pkt lb spv,
  getr regs 2%bv = W spv -> getr regs 4%bv = W TP -> getr regs 10%bv = W pkt -> getr regs 11%bv = W lb ->
  rt_ok M -> ic_ok M -> BFakeStack.fsrt_ok M fs T ctx thr -> BFakeStack.fsrt_wf fs T ctx thr -> uar_on M ->
  fs_wf fs -> 0 <= h < 2 ^ 64 -> cell BSEGS M fs 8 (W h) -> zeros M (fs + 4096) 16384 -> ring_wr M fs ->
  B_IMG_END <= spv - 336 -> spv < 2 ^ 63 -> spv mod 32 = 0 -> wr_ok BSEGS M (spv - 336) 336 ->
  (spv <= fs \/ fs + FS_SIZE <= spv - 336) -> (spv <= SB \/ HIMEM_BEG <= spv - 336) ->
  BFakeStack.fsrt_sep (spv - 336) 336 fs T ctx thr ->
  B_IMG_END <= pkt -> memrange pkt 56 -> pkt mod 8 = 0 -> zeros M (sha (pkt + 16)) 2 -> wr_ok BSEGS M (pkt + 16) 16 ->
  (spv <= pkt \/ pkt + 56 <= spv - 336) -> (pkt + 56 <= fs \/ fs + 1085440 <= pkt) ->
  let k := h mod 16384 in let FB := fs + 36864 + 64 * k in
  exists regs' M',
    msteps BSEGS (mkstF regs F fc (W 0x272638) M rom) (mkstF regs' F fc (W 0x272778) M' rom)
    /\ (forall r : reg, ~ In (ridx r) KS_r1 -> getr regs' r = getr regs r)
    /\ getr regs' 2%bv = W (spv - 128) /\ getr regs' 8%bv = W spv /\ getr regs' 9%bv = W (spv - 128)
    /\ getr regs' 10%bv = W 40 /\ getr regs' 11%bv = W 0x2d61f /\ getr regs' 12%bv = W 110
    /\ getr regs' 18%bv = W FB /\ getr regs' 19%bv = W lb /\ getr regs' 20%bv = W pkt /\ getr regs' 23%bv = W (sha FB)
    /\ getr regs' 24%bv = W FB /\ getr regs' 25%bv = W SB
    /\ (forall off r, In (off, r) WI_SLOTS -> cell BSEGS M' (spv - 128 + off) 8 (getr regs (Z_to_bv 5 (Z.of_nat r))))
    /\ cell BSEGS M' fs 8 (W (h + 1)) /\ cell BSEGS M' (fs + 4096 + k) 1 (W 1)
    /\ zeros M' (fs + 4096) k /\ zeros M' (fs + 4096 + k + 1) (16383 - k)
    /\ cell BSEGS M' (FB + 56) 8 (W (fs + 4096 + k))
    /\ cell BSEGS M' (pkt + 16) 8 (W 0) /\ cell BSEGS M' (pkt + 24) 8 (W 0)
    /\ (forall x, ~ FP_r1 fs spv pkt x -> M' x = M x) /\ mem_grows M M'.
Proof.
  intros regs F fc M rom fs T ctx thr h pkt lb spv H2 H4 H10 H11 Hrt Hic Hfsrt Hwf Huar Hfs Hh Chint Hz Hrwr
    HS1 HS2 HS3 Hw Hs1 Hs2 Hfsep P1 P2 P3 Zp Wp Sk1 Sk2 k FB.
  pose proof (rt_iface_real fs T ctx thr Hwf) as IF.
  pose (Post := fun (pc' : word) (l' : regfile) (M' : mem) =>
     pc' = W 0x272778 /\ same_except KS_r1 (lof regs) l'
     /\ (rget l' 2 = W (spv - 128) /\ rget l' 8 = W spv /\ rget l' 9 = W (spv - 128)
         /\ rget l' 10 = W 40 /\ rget l' 11 = W 0x2d61f /\ rget l' 12 = W 110
         /\ rget l' 18 = W FB /\ rget l' 19 = W lb /\ rget l' 20 = W pkt /\ rget l' 23 = W (sha FB)
         /\ rget l' 24 = W FB /\ rget l' 25 = W SB)
     /\ (forall off r, In (off, r) WI_SLOTS -> cell BSEGS M' (spv - 128 + off) 8 (rget (lof regs) r))
     /\ (cell BSEGS M' fs 8 (W (h + 1)) /\ cell BSEGS M' (fs + 4096 + k) 1 (W 1)
         /\ zeros M' (fs + 4096) k /\ zeros M' (fs + 4096 + k + 1) (16383 - k)
         /\ cell BSEGS M' (FB + 56) 8 (W (fs + 4096 + k))
         /\ cell BSEGS M' (pkt + 16) 8 (W 0) /\ cell BSEGS M' (pkt + 24) 8 (W 0))
     /\ unch M M' (FP_r1 fs spv pkt) /\ mem_grows M M').
  assert (HR : reach BSEGS rom (W 0x272638) (lof regs) M Post).
  { eapply (wpinit_r1_cps _ _ _ fs IF rom Post M pkt lb spv h);
      [ exact Hrt | split; assumption | exact Huar | exact Hfs | exact Hh | exact Chint | exact Hz | exact Hrwr
      | split; [exact HS1 | split; [exact HS2 | exact HS3]] | exact Hw | exact Hs1 | exact Hs2 | exact Hfsep
      | split; [exact P1 | split; [exact P2 | exact P3]] | exact Zp | exact Wp | split; [exact Sk1 | exact Sk2]
      | reflexivity | lof_reg | lof_reg | lof_reg | lof_reg | ].
    intros l' M' k0 FB0 Hl' Hse R2 R8 R9 R10 R11 R12 R18 R19 R20 R23 R24 R25 Hsv Ch Cf Z1 Z2 C56 Cp16 Cp24 HU HG.
    apply reach_done. unfold Post.
    split; [reflexivity|]. split; [exact Hse|].
    split; [repeat split; assumption|]. split; [exact Hsv|]. split; [repeat split; assumption|]. split; [exact HU | exact HG]. }
  destruct (reach_exF BSEGS rom _ _ F fc _ _ HR) as (pc' & regs' & l' & M' & Hms & HRR & HP).
  destruct HP as (-> & Hse & (R2 & R8 & R9 & R10 & R11 & R12 & R18 & R19 & R20 & R23 & R24 & R25) & Hsv
                  & (Ch & Cf & Z1 & Z2 & C56 & Cp16 & Cp24) & HU & HG).
  exists regs', M'. split; [exact Hms|].
  split; [intros r Hr; eapply same_except_getr; eassumption|].
  split; [reg_out HRR R2|]. split; [reg_out HRR R8|]. split; [reg_out HRR R9|]. split; [reg_out HRR R10|].
  split; [reg_out HRR R11|]. split; [reg_out HRR R12|]. split; [reg_out HRR R18|]. split; [reg_out HRR R19|].
  split; [reg_out HRR R20|]. split; [reg_out HRR R23|]. split; [reg_out HRR R24|]. split; [reg_out HRR R25|].
  split.
  { intros off r Hin. specialize (Hsv off r Hin).
    assert (Hr : (0 < r < 32)%nat).
    { unfold WI_SLOTS in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as _ <-; lia|]). contradiction. }
    rewrite rget_lof in Hsv by exact Hr. exact Hsv. }
  split; [exact Ch|]. split; [exact Cf|]. split; [exact Z1|]. split; [exact Z2|]. split; [exact C56|].
  split; [exact Cp16|]. split; [exact Cp24|].
  split; [exact HU | exact HG].
Qed.

(* [comment removed for export] *)
Theorem wpinit_r2_spec : forall regs F fc M rom fs pkt spv k (res : word) (sv : nat -> word),
  let FB := fs + 36864 + 64 * k in
  getr regs 8%bv = W spv -> getr regs 10%bv = res -> getr regs 18%bv = W FB -> getr regs 19%bv = W 0 ->
  getr regs 20%bv = W pkt -> getr regs 23%bv = W (sha FB) -> getr regs 24%bv = W FB -> getr regs 25%bv = W SB ->
  v_jalr (sv 1%nat) 0 = sv 1%nat ->
  fs_wf fs -> 0 <= k < 16384 ->
  (forall off r, In (off, r) WI_SLOTS -> cell BSEGS M (spv - 128 + off) 8 (sv r)) ->
  cell BSEGS M (FB + 56) 8 (W (fs + 4096 + k)) ->
  zeros M (fs + 4096) k -> zeros M (fs + 4096 + k + 1) (16383 - k) -> zeros M (sha (pkt + 40)) 1 ->
  B_IMG_END <= pkt -> memrange pkt 56 -> pkt mod 8 = 0 ->
  wr_ok BSEGS M (pkt + 40) 8 -> wr_ok BSEGS M FB 8 -> wr_ok BSEGS M (sha FB) 8 -> wr_ok BSEGS M (fs + 4096 + k) 1 ->
  B_IMG_END <= spv - 128 -> spv < 2 ^ 63 ->
  (spv <= fs \/ fs + FS_SIZE <= spv - 128) -> (spv <= SB \/ HIMEM_BEG <= spv - 128) ->
  (spv <= pkt \/ pkt + 56 <= spv - 128) -> (pkt + 56 <= fs \/ fs + 1085440 <= pkt) ->
  exists regs' M' a0v,
    msteps BSEGS (mkstF regs F fc (W 0x27277c) M rom) (mkstF regs' F fc (sv 1%nat) M' rom)
    /\ (forall r : reg, ~ In (ridx r) KS_r2 -> getr regs' r = getr regs r)
    /\ getr regs' 2%bv = W spv /\ getr regs' 10%bv = W a0v
    /\ (bv_unsigned res = 0 -> a0v = 0) /\ (bv_unsigned res <> 0 -> a0v = 1)
    /\ (forall off r, In (off, r) WI_SLOTS -> getr regs' (Z_to_bv 5 (Z.of_nat r)) = sv r)
    /\ cell BSEGS M' (pkt + 40) 8 res /\ zeros M' (fs + 4096) 16384
    /\ (forall x, ~ FP_r2 fs pkt k x -> M' x = M x) /\ mem_grows M M'.
Proof.
  intros regs F fc M rom fs pkt spv k res sv FB H8 H10 H18 H19 H20 H23 H24 H25 Hret Hfs Hk Hsaved C56 Z1 Z2 Zp
    P1 P2 P3 W1 W2 W3 W4 S1 S2 D1 D2 D3 D4.
  pose (Post := fun (pc' : word) (l' : regfile) (M' : mem) =>
     pc' = sv 1%nat /\ same_except KS_r2 (lof regs) l'
     /\ (exists a0v, rget l' 2 = W spv /\ rget l' 10 = W a0v /\ (bv_unsigned res = 0 -> a0v = 0) /\ (bv_unsigned res <> 0 -> a0v = 1))
     /\ (forall off r, In (off, r) WI_SLOTS -> rget l' r = sv r)
     /\ cell BSEGS M' (pkt + 40) 8 res /\ zeros M' (fs + 4096) 16384
     /\ unch M M' (FP_r2 fs pkt k) /\ mem_grows M M').
  assert (HR : reach BSEGS rom (W 0x27277c) (lof regs) M Post).
  { eapply (wpinit_r2_cps rom Post M fs pkt spv k res sv);
      [ exact Hfs | exact Hk | exact Hsaved | exact C56 | exact Z1 | exact Z2 | exact Zp
      | split; [exact P1 | split; [exact P2 | exact P3]]
      | split; [exact W1 | split; [exact W2 | split; [exact W3 | exact W4]]]
      | split; [exact S1 | exact S2]
      | split; [exact D1 | split; [exact D2 | split; [exact D3 | exact D4]]]
      | reflexivity | lof_reg | lof_reg | lof_reg | lof_reg | lof_reg | lof_reg | lof_reg | lof_reg | ].
    intros l' M' a0v Hl' Hse R2 R10 Ha0 Ha1 Hsv Cres Hz HU HG. rewrite Hret.
    apply reach_done. unfold Post.
    split; [reflexivity|]. split; [exact Hse|]. split; [exists a0v; repeat split; assumption|].
    split; [exact Hsv|]. split; [exact Cres|]. split; [exact Hz|]. split; [exact HU | exact HG]. }
  destruct (reach_exF BSEGS rom _ _ F fc _ _ HR) as (pc' & regs' & l' & M' & Hms & HRR & HP).
  destruct HP as (-> & Hse & (a0v & R2 & R10 & Ha0 & Ha1) & Hsv & Cres & Hz & HU & HG).
  exists regs', M', a0v. split; [exact Hms|].
  split; [intros r Hr; eapply same_except_getr; eassumption|].
  split; [reg_out HRR R2|]. split; [reg_out HRR R10|]. split; [exact Ha0|]. split; [exact Ha1|].
  split.
  { intros off r Hin. specialize (Hsv off r Hin).
    assert (Hr : (0 < r < 32)%nat).
    { unfold WI_SLOTS in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as _ <-; lia|]). contradiction. }
    rewrite (rrel_getr regs' l' r HRR) by exact Hr. exact Hsv. }
  split; [exact Cres|]. split; [exact Hz|]. split; [exact HU | exact HG].
Qed.

Print Assumptions wpinit_r1_spec.
Print Assumptions wpinit_r2_spec.
