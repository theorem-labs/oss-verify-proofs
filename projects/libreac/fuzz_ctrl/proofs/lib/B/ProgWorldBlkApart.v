(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/ProgWorldBlkApart.v (a working branch b6421486bf8, blob 22f3e61fbe0 (the blob this tree had at release c5e779efe8c), read by git show): the same lemma ctl_block_apart_fs, the same Section BlockApartFs, the same Requires and the same proof, line for line.  The statement B.ProgWorld.ctl_block_apart_fs_stmt is character-identical to A's lib/A/ProgWorld.v:1225-1235.  Differences from A: the module path A.ProgWorld -> B.ProgWorld (Require and the statement's name), and A's ITERATION-ONLY status sentence, which is not carried.  Every other module named is a core lib.Reusable module that A names (YK11, YM05, YG00, YG0f, YG0n, YG0d, YG0s).  The statement and proof are image-generic: no image constant appears. *)
(* lib/B/ProgWorldBlkApart.v -- proof of ProgWorld.v's ctl_block_apart_fs_stmt (Section BlockApartFs, item 17).
   rule 24: no function proved.  A bridge lemma over the core's world (AR / ablocks / layout_ok / sec_placed), not a
   proof of any binary function. *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorld.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG00 YG0f YG0n YG0d YG0s.
Import ListNotations.
Local Open Scope Z_scope.

Section BlockApartFs.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.

(* ctl_block_apart_fs.  An ablocks entry (p, n) is the user range of a live chunk k (YG0s.In_ablocks), and
   YG0s.chunk_facts (from AR's ARm: Wf chunk_ok, layout_ok, sec_placed) puts [p, p + req_size n) inside
   [ck_base k, ck_base k + ck_extent k).  That extent is
   - PPrim: inside its class region, which lies in the primary reservation (ly_prim, kPrimResvSize)
     (YG0s.region_in_prim); layout_ok's lo_disj keeps that reservation apart from (ly_F, kFakeStackSize), both being
     static extents;
   - PSec r: inside the section mapping (ly_sec r, sec_map_size), an element of sec_extents; sec_placed keeps
     sec_extents ++ static_extents pairwise disjoint, so the mapping is apart from (ly_F, kFakeStackSize). *)
Lemma ctl_block_apart_fs : B.ProgWorld.ctl_block_apart_fs_stmt B.
Proof.
  intros _ ly S W m md p n HAR Hin.
  pose proof HAR as (M & _).
  pose proof (lib.Reusable.YG0n.am_layout _ _ _ _ M) as LO.
  apply lib.Reusable.YG0s.In_ablocks in Hin as (k & Hk & _ & Hu & Hn). subst p n.
  pose proof (lib.Reusable.YG0s.chunk_facts B ly S _ k M Hk) as (_ & _ & _ & G4 & G5 & _ & _ & G8 & GG).
  destruct (lib.Reusable.YG00.ck_beg k) as [|off|r o|c q] eqn:Eb; try solve [destruct GG].
  - cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal).
    pose proof (lib.Reusable.YG0s.region_in_prim ly (lib.Reusable.YG00.prim_class off) LO ltac:(lia)) as (R1 & R2 & _).
    pose proof (lib.Reusable.YG0s.pairwise_In lib.Reusable.YG0f.zdisjoint (lib.Reusable.YG0f.static_extents ly)
      (lib.Reusable.YG0f.ly_prim ly, lib.Reusable.YG0f.kPrimResvSize)
      (lib.Reusable.YG0f.ly_F ly, lib.Reusable.YG0f.kFakeStackSize)
      [(lib.Reusable.YG0f.ly_prim ly, lib.Reusable.YG0f.kPrimResvSize)] (tl (lib.Reusable.YG0f.static_extents ly))
      eq_refl (lib.Reusable.YG0f.lo_disj _ LO) (or_introl eq_refl)
      ltac:(unfold lib.Reusable.YG0f.static_extents, lib.Reusable.YG0f.owned_extents; cbn; tauto)) as DJ.
    unfold lib.Reusable.YG0f.zdisjoint in DJ. cbn [fst snd] in DJ.
    lia.
  - destruct GG as (_ & _ & Gbase & Gext & Gin & _).
    pose proof (lib.Reusable.YG0s.pairwise_In lib.Reusable.YG0f.zdisjoint _ _
      (lib.Reusable.YG0f.ly_F ly, lib.Reusable.YG0f.kFakeStackSize) _ (lib.Reusable.YG0f.static_extents ly)
      eq_refl (proj2 (lib.Reusable.YG0n.am_placed _ _ _ _ M)) Gin
      ltac:(unfold lib.Reusable.YG0f.static_extents, lib.Reusable.YG0f.owned_extents; cbn; tauto)) as DJ.
    unfold lib.Reusable.YG0f.zdisjoint in DJ. cbn [fst snd] in DJ.
    unfold lib.Reusable.YG00.kPage in *.
    lia.
Qed.

End BlockApartFs.
Print Assumptions ctl_block_apart_fs.
