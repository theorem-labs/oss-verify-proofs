(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import
  PropExec AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore CxPlan CxPlanSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxRel CxAcctShape CxNodesLibE.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Section SniffOff.
  Variables (SEGS : list Segment) (A : atable) (nx0 : nat) (LIMIT : Z).
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable ISP : Z.
  Variable FS0 : Fs.Fs.
  Hypothesis TAB : 2 ^ 64 <= sniff_tab A + 24.

  Theorem x_stmt_sniff_off : x_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 XSniff.
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn _. exfalso.
    cbn [node_x] in Hn. rewrite summary_sniff_eq in Hn. unfold summary_sniff_ref in Hn.
    destruct (negb (pc cs =? x_sniff A)); [discriminate|].
    destruct (ret_lit cs); [|discriminate].
    destruct (split_lit (reg cs 10)) as [bb bk]. destruct (split_lit (eaddz (reg cs 2) (-8))) as [qb qk].
    destruct (xhi (kn cs) (reg cs 11)) as [nhi|]; [|discriminate].
    destruct (xhi (kn cs) (reg cs 10)) as [bhi|]; [|discriminate].
    destruct (xlo (kn cs) (reg cs 2)) as [splo|] eqn:Hsplo; [|discriminate].
    destruct (xhi (kn cs) (reg cs 2)) as [sphi|]; [|discriminate].
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    clear Hn. repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H end.
    match goal with H : (sniff_tab A + 16 + 8 <=? splo) = true |- _ => apply Z.leb_le in H; rename H into HT end.
    pose proof (xlo_sound SEGS E _ (kn cs) (reg cs 2) splo (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) Hsplo) as X.
    pose proof (u64_range (edenot E (reg cs 2))). lia.
  Qed.
End SniffOff.
