(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk AgentLib Hoare.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanRPLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanDepotMem AsanDepotInv AsanDepotWalkP.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require PropExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastV.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastVK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastVS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Definition PUT_ENTRY : word := 0x74d04%bv.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition put_clob (r : reg) : Prop :=
  r = 5%bv \/ r = 6%bv \/ r = 10%bv \/ r = 11%bv \/ r = 12%bv \/ r = 13%bv \/ r = 14%bv \/ r = 15%bv \/ r = 16%bv.

Lemma put_clob_not : forall r, ~ put_clob r ->
  r <> 5%bv /\ r <> 6%bv /\ r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv /\ r <> 15%bv /\ r <> 16%bv.
Proof. unfold put_clob. intros r H. repeat split; intros ->; apply H; tauto. Qed.

Theorem put_spec :
  forall (mem rom : word -> option byte) (usp T w size tag : Z) (bs : list byte) (ret : word)
         (B P ncap fcap k : Z) (regs : bvmap 5 word),
    depot_inv B P ncap fcap (k + 1) mem -> 0 <= k ->
    (* [comment removed for export] *)
    2 ^ 32 <= usp - 224 -> usp < 2 ^ 64 -> okr mem (usp - 224) 224 ->
    (* [comment removed for export] *)
    2 ^ 32 <= T -> T + 8 * size < 2 ^ 64 ->
    rdn SEGS mem (Z_to_bv 64 T) (Z.to_nat (8 * size)) = Some bs ->
    (T + 8 * size <= usp - 224 \/ usp <= T) ->
    w = size + tag * 2 ^ 32 -> 1 <= size <= 255 -> 0 <= tag < 256 ->
    (* [comment removed for export] *)
    (usp <= B \/ B + 16 * ncap <= usp - 224) -> (usp <= P \/ P + 8 * fcap <= usp - 224) ->
    (T + 8 * size <= B \/ B + 16 * ncap <= T) -> (T + 8 * size <= P \/ P + 8 * fcap <= T) ->
    ret_ok ret ->
    getr regs 1 = ret -> getr regs 2 = Z_to_bv 64 usp -> getr regs 10 = Z_to_bv 64 T -> getr regs 11 = Z_to_bv 64 w ->
    exists (regs' : bvmap 5 word) (mem' : word -> option byte) (id : Z),
         msteps SEGS (mkst regs PUT_ENTRY mem rom) (mkst regs' ret mem' rom)
      /\ depot_inv B P ncap fcap k mem'
      /\ getr regs' 10 = Z_to_bv 64 id /\ 0 <= id < ncap
      /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ret
      /\ (forall r, ~ put_clob r -> getr regs' r = getr regs r)
      /\ (forall x : word, ~ (usp - 224 <= bv_unsigned x < usp) -> ~ depot_foot B P ncap fcap (bv_unsigned x) -> mem' x = mem x)
      /\ mem_grows mem mem'.
Proof.
  intros mem rom usp T w size tag bs ret B P ncap fcap k regs
         (d & C & G & Hk & Hn & Htf & Hsk & OB & OP) Hk0 Husp1 Husp2 Hstk HT1 HT2 HTrd HTstk Hw Hsz Htg HBstk HPstk HBT HPT Hret H1 H2 H10 H11.
  pose proof C as (Ctab & Cn & Cmap & Cnodes & Ctf & CP & Cst & Cr).
  pose proof G as (GB1 & GB2 & GN & GP1 & GP2 & GF & GBP).
  destruct d as [n tf st tab lnk hsh]. cbn [d_n d_tf d_st d_tab d_lnk d_hsh] in *.
  assert (Hroom : 0 <= tf /\ tf + 256 < 2 ^ 20 /\ 0 <= st /\ st + 256 < 2 ^ 20) by nia.
  destruct (put_walk mem rom usp T w size tag bs ret n B P tf st tab lnk hsh) with (regs := regs)
    as (r' & h & found & RUN & RES & R2 & R1 & RR); try assumption; try (ltac2:(LK.k [@Husp1; @Husp2; @HT1; @HT2; @HTstk; @Hw; @Hsz; @Htg; @HBstk; @HPstk; @HBT; @HPT; @GN; @GF; @GBP; @Hn; @Htf; @Hk0; @Cr; @Hroom; @GB1; @GB2; @GP1; @GP2]); lia).
  { eapply okr_sub; [exact OB | lia | lia]. }
  { eapply okr_sub; [exact OP | lia | lia]. }
  unfold PUT_ENTRY.
  pose proof (u64_range h) as Hh.
  assert (Hbk : 0 <= bv_unsigned h mod 2 ^ 20 < 2 ^ 20) by (apply Z.mod_pos_bound; lia).
  destruct found.
  - (* [comment removed for export] *)
    destruct RES as (id & Hid & R10).
    exists r'. eexists. exists id. split; [exact RUN|].
    assert (AG : forall x : word, depot_foot B P ncap fcap (bv_unsigned x) ->
              put_frame mem usp T w ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
                        (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) x = mem x).
    { intros x Hx. unfold depot_foot in Hx. apply (pf_out mem usp T w size bs ret); try assumption; try lia. }
    split; [|split; [exact R10 | split; [lia | split; [exact R2 | split; [exact R1 | split; [|split]]]]]].
    + eapply depot_inv_weaken with (k := k + 1); [|lia].
      eapply depot_inv_agree; [exists (DS n tf st tab lnk hsh); split; [exact C|]; split; [exact G|]; repeat split; assumption | exact AG | apply pf_grows; try assumption; lia].
    + intros r Hr. pose proof (put_clob_not r Hr) as (?&?&?&?&?&?&?&?&?). apply RR; assumption.
    + intros x Hx _. pose proof (u64_range x). apply (pf_out mem usp T w size bs ret); try assumption; lia.
    + apply pf_grows; try assumption; lia.
  - (* [comment removed for export] *)
    exists r'. eexists. exists (n + 1). split; [exact RUN|].
    split; [|split; [exact RES | split; [lia | split; [exact R2 | split; [exact R1 | split; [|split]]]]]].
    + exists (d_ins size n tf st tab lnk hsh h (bv_unsigned h mod 2 ^ 20)).
      split; [apply ins_cells; try assumption; try (ltac2:(LK.k [@Husp1; @Husp2; @HT1; @HT2; @HTstk; @Hw; @Hsz; @Htg; @HBstk; @HPstk; @HBT; @HPT; @GN; @GF; @GBP; @Hh; @Hn; @Htf; @Hk0; @Cr; @Hroom; @GB1; @GB2; @GP1; @GP2]); lia); (ltac2:(LK.k [@Husp1; @Husp2; @HT1; @HT2; @HTstk; @Hw; @Hsz; @Htg; @HBstk; @HPstk; @HBT; @HPT; @GN; @GF; @GBP; @Hh; @Hn; @Htf; @Hk0; @Cr; @Hroom; @GB1; @GB2; @GP1; @GP2]); nia)|].
      split; [exact G|]. cbn [d_n d_tf d_st d_ins]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; (eapply okr_grows; [apply ins_grows | assumption]).
    + intros r Hr. pose proof (put_clob_not r Hr) as (?&?&?&?&?&?&?&?&?). apply RR; assumption.
    + intros x Hx Hf. apply (ins_out mem usp T w size tag bs ret n B P tf st tab); try assumption; try lia.
      unfold ins_written, depot_foot in *. pose proof (u64_range x). intros HW.
      destruct HW as [W|[W|[W|[W|[W|[W|W]]]]]]; [exfalso; apply Hx; exact W | apply Hf ..];
        [left; (ltac2:(LK.k [@Hn; @Htf; @Hk0; @Husp1; @HT1; @HTstk; @Hsz; @HBstk; @HPstk; @HBT; @HPT; @Cr; @GB1; @GN; @GP1; @GF; @GBP; @Hroom; @Hh; @Hbk; @Hf; @W; @Hx]); lia) | left; (ltac2:(LK.k [@Hn; @Htf; @Hk0; @Husp1; @HT1; @HTstk; @Hsz; @HBstk; @HPstk; @HBT; @HPT; @Cr; @GB1; @GN; @GP1; @GF; @GBP; @Hroom; @Hh; @Hbk; @Hf; @W; @Hx]); lia) | right; left; (ltac2:(LK.k [@Hn; @Htf; @Hk0; @Husp1; @HT1; @HTstk; @Hsz; @HBstk; @HPstk; @HBT; @HPT; @Cr; @GB1; @GN; @GP1; @GF; @GBP; @Hroom; @Hh; @Hbk; @Hf; @W; @Hx]); lia) | right; right; left; (ltac2:(LK.k [@Hn; @Htf; @Hk0; @Husp1; @HT1; @HTstk; @Hsz; @HBstk; @HPstk; @HBT; @HPT; @Cr; @GB1; @GN; @GP1; @GF; @GBP; @Hroom; @Hh; @Hbk; @Hf; @W; @Hx]); lia) | right; right; left; (ltac2:(LK.k [@Hn; @Htf; @Hk0; @Husp1; @HT1; @HTstk; @Hsz; @HBstk; @HPstk; @HBT; @HPT; @Cr; @GB1; @GN; @GP1; @GF; @GBP; @Hroom; @Hh; @Hbk; @Hf; @W; @Hx]); lia) | right; right; right; (ltac2:(LK.k [@Hn; @Htf; @Hk0; @Husp1; @HT1; @HTstk; @Hsz; @HBstk; @HPstk; @HBT; @HPT; @Cr; @GB1; @GN; @GP1; @GF; @GBP; @Hroom; @Hh; @Hbk; @Hf; @W; @Hx]); lia)].
    + apply ins_grows.
Qed.

