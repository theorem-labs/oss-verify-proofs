(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import Prelim STree Malloc MallocCtrl Realloc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad Prog.

Set Keyed Unification.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Local Notation MP := (Monad.M PState).

Inductive remap_ans : Type := RmErr (e : Z) | RmSame | RmAt (nb : Z).

Definition remap_tail_zs (base oldl needed : Z) : list (word * word) :=
  if oldl <? needed then [(wa (base + oldl), Z_to_bv 64 (needed - oldl))] else [].

Definition dec_mremap (avoidx avoid : list (Z * Z)) (oldb oldl needed : Z) (rsp : resp) : option remap_ans :=
  match rsp with
  | mkEffectU r [] zs us cs [] =>
      match errno_of r with
      | Some e => match zs, us, cs with [], [], [] => Some (RmErr e) | _, _, _ => None end
      | None =>
        let nb := bv_unsigned r in
        if nb =? oldb then

          match cs with
          | [] =>
            if needed <? oldl then
              (if listNN_eqb us [(wa (oldb + needed), Z_to_bv 64 (oldl - needed))] && match zs with [] => true | _ => false end
               then Some RmSame else None)
            else
              (if listNN_eqb zs (remap_tail_zs oldb oldl needed) && match us with [] => true | _ => false end
                  && (oldb + needed <=? alloc_ceiling) && ranges_free avoidx (oldb + oldl) (needed - oldl)
               then Some RmSame else None)
          | _ => None
          end
        else

          match cs with
          | [mkCopy src dst len] =>
              if bv_eqb src (wa oldb) && bv_eqb dst r && bv_eqb len (Z_to_bv 64 oldl)
                 && listNN_eqb zs (remap_tail_zs nb oldl needed)
                 && listNN_eqb us [(wa oldb, Z_to_bv 64 oldl)]
                 && (nb mod 4096 =? 0) && (0 <? nb) && (nb + needed <=? alloc_ceiling) && ranges_free avoid nb needed
                 && (oldl <? needed)
              then Some (RmAt nb) else None
          | _ => None
          end
      end
  | _ => None
  end.

Definition realloc_move (p : bptr) (n : Z) : MP (option bptr) :=
  r <- raw_malloc n ;;
  match r with
  | None => mret None
  | Some p' => raw_free p ;;; mret (Some p')
  end.

Definition realloc_remap (p : bptr) (n : Z) (cs : mstate) (rid : N) (g : aptr) (oldb oldl needed : Z) : MP (option bptr) :=
  if oldl =? needed then (mupd (set_m (remap_update cs rid g oldb needed)) ;;; mret (Some p))
  else
    (a <- msys (NMremap oldb oldl needed)
               (dec_mremap (live_ranges_except cs rid) (live_ranges cs) oldb oldl needed) ;;
     match a with
     | RmErr _ => realloc_move p n
     | RmSame => mupd (set_m (remap_update cs rid g oldb needed)) ;;; mret (Some p)
     | RmAt nb => mupd (set_m (remap_update cs rid g nb needed)) ;;; mret (Some p)
     end).

Definition realloc_body (p : bptr) (A n : Z) (cs : mstate) : MP (option bptr) :=
  match realloc_case cs (fst p) A n with
  | RcInPlace => mret (Some p)
  | RcRemap rid g oldb oldl needed => realloc_remap p n cs rid g oldb oldl needed
  | RcMove => realloc_move p n
  end.

Definition raw_realloc (p : bptr) (A n : Z) : MP (option bptr) :=
  s <- mget ;; realloc_body p A n (ps_m s).

Definition realloc_addr (s s' : PState) (p : bptr) (A : Z) : Z := conc (ps_m s') (fst p) + (A - conc (ps_m s) (fst p)).

Lemma dec_mremap_Some : forall avoidx avoid B OL NL rsp a,
  dec_mremap avoidx avoid B OL NL rsp = Some a ->
  match a with
  | RmErr e => rsp = efferr e /\ 1 <= e <= 4095
  | RmSame =>
      rsp = mkEffectU (Z_to_bv 64 B) [] (if NL <? OL then [] else remap_tail_zs B OL NL)
                      (if NL <? OL then [(wa (B + NL), Z_to_bv 64 (OL - NL))] else []) [] []
      /\ 0 <= B < 2^64
      /\ (OL <= NL -> B + NL <= alloc_ceiling /\ ranges_free avoidx (B + OL) (NL - OL) = true)
  | RmAt nb =>
      rsp = mkEffectU (Z_to_bv 64 nb) [] [(wa (nb + OL), Z_to_bv 64 (NL - OL))] [(wa B, Z_to_bv 64 OL)]
                      [mkCopy (wa B) (Z_to_bv 64 nb) (Z_to_bv 64 OL)] []
      /\ nb <> B /\ nb mod 4096 = 0 /\ 0 < nb /\ nb + NL <= alloc_ceiling /\ ranges_free avoid nb NL = true /\ OL < NL
  end.
Proof.
  intros avoidx avoid B OL NL [r ws zs us cs ci] a H. unfold dec_mremap in H.
  destruct ws; [|discriminate]. destruct ci; [|discriminate].
  pose proof (bv_unsigned_in_range 64 r) as RR. unfold bv_modulus in RR. change (2 ^ Z.of_N 64) with (2^64) in RR.
  assert (ER : Z_to_bv 64 (bv_unsigned r) = r) by (apply Z_to_bv_bv_unsigned).
  destruct (errno_of r) eqn:E.
  { destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
    injection H as <-. apply errno_of_Some in E as [E' He]. split; [|exact He]. unfold efferr, eff0. rewrite <- E'. reflexivity. }
  destruct (Z.eqb_spec (bv_unsigned r) B) as [EB|NB].
  - destruct cs; [|discriminate].
    assert (r = Z_to_bv 64 B) by (rewrite <- EB; symmetry; exact ER). subst r. rewrite ?EB in H. rewrite ?EB in RR.
    destruct (Z.ltb_spec NL OL) as [LT|GE].
    + destruct (listNN_eqb us _) eqn:U; [|discriminate]. destruct zs; [|discriminate]. cbn [andb] in H. injection H as <-.
      apply listNN_eqb_eq in U. subst us. split; [reflexivity|]. split; [lia|]. intros; lia.
    + destruct (listNN_eqb zs _) eqn:U; [|discriminate]. destruct us; [|discriminate].
      destruct (Z.leb_spec0 (B + NL) alloc_ceiling); [|discriminate].
      destruct (ranges_free avoidx (B + OL) (NL - OL)) eqn:RF; [|discriminate].
      cbn [andb] in H. injection H as <-. apply listNN_eqb_eq in U. subst zs. split; [reflexivity|]. split; [lia|]. intros; split; [lia| reflexivity].
  - destruct cs as [|[src dst len] [|]]; try discriminate.
    destruct (bv_eqb src (wa B)) eqn:E1; [|discriminate]. destruct (bv_eqb dst r) eqn:E2; [|discriminate].
    destruct (bv_eqb len (Z_to_bv 64 OL)) eqn:E3; [|discriminate].
    destruct (listNN_eqb zs _) eqn:U1; [|discriminate]. destruct (listNN_eqb us _) eqn:U2; [|discriminate].
    destruct (Z.eqb_spec (bv_unsigned r mod 4096) 0); [|discriminate]. destruct (Z.ltb_spec0 0 (bv_unsigned r)); [|discriminate].
    destruct (Z.leb_spec0 (bv_unsigned r + NL) alloc_ceiling); [|discriminate]. destruct (ranges_free avoid (bv_unsigned r) NL) eqn:RF; [|discriminate].
    destruct (Z.ltb_spec OL NL); [|discriminate].
    cbn [andb] in H. injection H as <-.
    apply Fs.bv_eqb_eq in E1. apply Fs.bv_eqb_eq in E2. apply Fs.bv_eqb_eq in E3. apply listNN_eqb_eq in U1. apply listNN_eqb_eq in U2. subst.
    rewrite ER. unfold remap_tail_zs. replace (OL <? NL) with true by (symmetry; apply Z.ltb_lt; lia). repeat split; auto.
Qed.

End CEIL.
