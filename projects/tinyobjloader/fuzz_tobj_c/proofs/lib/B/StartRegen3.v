(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3: the join of segment 7's two per-CONFIG_RSEQ exits (B/o5.v Start7States [K18r r]) into the one exit [K18] both reach, proved a weakening: the auxv tail the CONFIG_RSEQ layout adds is split off and dropped, its memory taken into the valuation's memory map, then the entailment checked in the build forgets what the two values do not share; the dropped tail kept clear of the argument region's parity gap by the stack pointer's and the random bytes' 16-byte alignment; with the launch's head equation the memory map present on the dropped tail, ARG_TAIL, its bytes readable in the auxv object, tail18_present. *)
(* After musl malloc(40) has walked the auxv to AT_NULL (B/n1.v [run_I], per CONFIG_RSEQ), nothing in
   the start-up reads the auxv again (its cells are already forgotten in malloc's posts, B/ng.v
   [O_auxvF]).  The two exits [K18r false] and [K18r true] then differ in the auxv object's length: 432
   bytes, or 464 with CONFIG_RSEQ (AT_RSEQ_FEATURE_SIZE and AT_RSEQ_ALIGN before AT_NULL).  [K18_join]
   makes the one exit [K18] from either:
   - r = true: the auxv object is split at 432 ([SPA_split]), its tail [432, 464) moved last
     ([SPA_move_lastX]) and dropped ([SPA_unobj]: the valuation's memory map takes the machine's bytes
     on the dropped range, [rho_absorb]);
   - both: [K18] is entailed ([SPA_entails]; B/o5.v Start7States [K18_join_ent], checked in the build).
   No fact is added.  The valuation's memory map changes only on the dropped tail, which lies below the
   random bytes' object (disjoint from the auxv object in the state) and above the shadow band
   ([HMB3]).  This unit's argument region (B/n1.v StartALibS [ARGF]) also holds the head's parity gap,
   [ARG_GAP] bytes just below the random bytes; the tail stays below that gap because the stack pointer
   and the random bytes are both 16-byte aligned (the launch's layout, Lib/InitState.v [nums]: the
   head's items and the gap fill whole 16-byte units).  So the memory map keeps the argument region
   ([ARGF]) and every address below [HMB3] (the shadow band). *)
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymSummary Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Code KxA n8 n1 n5 n9 o5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.MuslMallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartArgF.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartALibS.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o5.Start7States.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

(* The shadow band's end (kHighMemBeg of B/Start7.v): every shadow address lies below it. *)
Definition HMB3 : Z := 0x10007fff8000.

Lemma U_AUXV18 : forall rho : valuation, arg_layout rho ->
  bv_unsigned (eval rho AUXV18)
  = bv_unsigned (rw rho 1%positive) + 8 * bv_unsigned (rw rho 2%positive) + 8 * bv_unsigned (rw rho 3%positive) + 24.
Proof.
  intros rho (L1 & L2 & L3 & _). unfold AUXV18. cbn [eval].
  pose proof (urange (rw rho 1%positive)) as U1. pose proof (urange (rw rho 2%positive)) as U2.
  pose proof (urange (rw rho 3%positive)) as U3.
  assert (S2 : bv_unsigned (alu64 ALU_SLL (rw rho 2%positive) (Z_to_bv 64 3)) = 8 * bv_unsigned (rw rho 2%positive))
    by (apply U_sll3; lia).
  assert (S3 : bv_unsigned (alu64 ALU_SLL (rw rho 3%positive) (Z_to_bv 64 3)) = 8 * bv_unsigned (rw rho 3%positive))
    by (apply U_sll3; lia).
  assert (A1 : bv_unsigned (alu64 ALU_ADD (rw rho 1%positive) (alu64 ALU_SLL (rw rho 2%positive) (Z_to_bv 64 3)))
               = bv_unsigned (rw rho 1%positive) + 8 * bv_unsigned (rw rho 2%positive)).
  { rewrite U_add_words by (rewrite S2; lia). rewrite S2. reflexivity. }
  assert (A2 : bv_unsigned (alu64 ALU_ADD (alu64 ALU_ADD (rw rho 1%positive) (alu64 ALU_SLL (rw rho 2%positive) (Z_to_bv 64 3)))
                                  (alu64 ALU_SLL (rw rho 3%positive) (Z_to_bv 64 3)))
               = bv_unsigned (rw rho 1%positive) + 8 * bv_unsigned (rw rho 2%positive) + 8 * bv_unsigned (rw rho 3%positive)).
  { rewrite U_add_words by (rewrite A1, S3; lia). rewrite A1, S3. reflexivity. }
  rewrite (U_add_small _ 24) by (rewrite ?A2; lia). rewrite A2. reflexivity.
Qed.

(* In [K18r true], the auxv object ends at least 464 bytes after its start and at or below the random
   bytes' object; with the stack pointer and the random bytes 16-byte aligned, the parity gap
   [ARG_GAP rho] bytes below the random bytes starts at or above the auxv's end.  So its tail
   [432, 464) is neither in the argument region nor below [HMB3]. *)
Lemma tail18_clear : forall (rho : valuation) (tp : list word) (w : world) (mo : Model) (Bx : Z) (a : word),
  arg_layout rho ->
  bv_unsigned (rw rho 1%positive) mod 16 = 0 -> bv_unsigned (rw rho 6%positive) mod 16 = 0 ->
  SPA segsA (KxA mo Bx) (K18r true) rho tp w ->
  in_ranges rho [otail18] a -> ~ (ARGF rho a \/ bv_unsigned a < HMB3).
Proof.
  intros rho tp w mo Bx a HAL A16 R16 Hsp Hin.
  pose proof K18S1_facts as (_ & _ & _ & _ & _ & _ & TB & TL & TH).
  pose proof K18_auxrand as (EAUX & RB & RL & RH & RLT & RNE & H432 & H464 & HFACT).
  pose proof (U_AUXV18 rho HAL) as UA.
  pose proof HAL as (L1 & L2 & L3 & L5 & L4 & L6 & L7 & L8).
  pose proof (urange (rw rho 1%positive)). pose proof (urange (rw rho 2%positive)). pose proof (urange (rw rho 3%positive)).
  pose proof (urange (rw rho 4%positive)). pose proof (urange (rw rho 5%positive)). pose proof (urange (rw rho 6%positive)).
  pose proof (urange a).
  destruct Hsp as [(Hsm & _) _].
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hpd & _) & HF).
  cbn [ax_S K18r] in Hpd, HF.
  (* the auxv object lies above the shadow band *)
  assert (HLO : 140735340871680 <= bv_unsigned (eval rho AUXV18)).
  { apply existsb_exists in HFACT as (g & Hg & He). apply sprop_eqb_sound in He. subst g.
    pose proof (proj1 (Forall_forall _ _) HF _ Hg) as X. cbn [holds eval] in X.
    rewrite Z_to_bv_unsigned in X. rewrite bv_wrap_small in X by (change (bv_modulus 64) with (2 ^ 64); lia). exact X. }
  (* the auxv object and the random bytes' object are disjoint *)
  set (iA := aux_at (K18Sr true)) in *. set (iR := rand_at (K18Sr true)) in *.
  set (oR := nth iR (ss_objs (K18Sr true)) odummy18) in *.
  rewrite H464 in EAUX.
  assert (ER : nth_error (ss_objs (K18Sr true)) iR = Some oR)
    by (unfold oR; apply nth_error_nth'; apply Nat.ltb_lt; exact RLT).
  apply Nat.eqb_neq in RNE.
  assert (RA : obj_range rho (mkObj AUXV18 (SLit 0) (SLit 464) [] DUnknown)
               = (bv_unsigned (eval rho AUXV18) + 0, bv_unsigned (eval rho AUXV18) + 464)).
  { unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia. reflexivity. }
  assert (RR : obj_range rho oR = (bv_unsigned (rw rho 6%positive) + 0, bv_unsigned (rw rho 6%positive) + 16)).
  { unfold obj_range, obj_lo_of, obj_hi_of. rewrite RB, RL, RH. cbn [eval]. rewrite !soff_lit_small by lia. reflexivity. }
  assert (DIS : bv_unsigned (eval rho AUXV18) + 464 <= bv_unsigned (rw rho 6%positive)).
  { destruct (Nat.lt_total iA iR) as [Hlt|[Heq|Hlt]]; [| exfalso; apply RNE; symmetry; exact Heq |].
    - pose proof (proj1 (pairwise_disjoint_nth rho _) Hpd iA iR _ _ Hlt EAUX ER) as D.
      rewrite RA, RR in D. unfold ranges_disjoint in D. cbn [fst snd] in D. lia.
    - pose proof (proj1 (pairwise_disjoint_nth rho _) Hpd iR iA _ _ Hlt ER EAUX) as D.
      rewrite RA, RR in D. unfold ranges_disjoint in D. cbn [fst snd] in D. lia. }
  (* the parity gap starts at or above the auxv's end: the head [sp, auxv) holds argc + envc + 3
     words, the gap is 8 bytes when that count is odd, and the 464 auxv bytes fill 29 whole units *)
  assert (GAP : bv_unsigned (eval rho AUXV18) + 464 <= bv_unsigned (rw rho 6%positive) - ARG_GAP rho).
  { unfold ARG_GAP. rewrite UA in DIS |- *.
    set (n := bv_unsigned (rw rho 2%positive) + bv_unsigned (rw rho 3%positive) + 3) in *.
    pose proof (Z.mod_pos_bound n 2 ltac:(lia)) as GM. pose proof (Z.div_mod n 2 ltac:(lia)) as GD.
    pose proof (Z.div_mod (bv_unsigned (rw rho 1%positive)) 16 ltac:(lia)) as D1.
    pose proof (Z.div_mod (bv_unsigned (rw rho 6%positive)) 16 ltac:(lia)) as D6.
    rewrite A16 in D1. rewrite R16 in D6. unfold n in GM, GD. lia. }
  (* the tail's range *)
  destruct Hin as (o & [<-|[]] & Ha1 & Ha2).
  unfold obj_range, obj_lo_of, obj_hi_of in Ha1, Ha2. rewrite TB, TL, TH in Ha1, Ha2.
  unfold MID18 in Ha1, Ha2. rewrite H432 in Ha1, Ha2. rewrite H464 in Ha1, Ha2.
  cbn [fst snd] in Ha1, Ha2. rewrite !soff_lit_small in Ha1, Ha2 by lia.
  pose proof (ARG_GAP_bound rho) as GB.
  intros [[Hge [Hlt|[[Hg1 Hg2]|[[Hp1 Hp2]|[Hs1 Hs2]]]]]|Hhm]; unfold HMB3 in *; lia.
Qed.

(* The tail [432, 464) of [K18r true]'s auxv object is readable in the virtual memory the join absorbs it
   from: the state matches the whole auxv object, so each of its bytes is readable (Fw3/SymSoundM.v
   [obj_byte_readable]), and the object lies above the image (its fact on [AUXV18]). *)
Lemma tail18_present : forall (rho : valuation) (tp : list word) (tr : list event) (ms : machine_state) (md : Model)
    (mo : Model) (Bx : Z) (a : word),
  arg_layout rho ->
  SPA segsA (KxA mo Bx) (K18r true) rho tp (tr, mkCfg ms md) ->
  in_ranges rho [otail18] a -> ms_mem (vms md tp ms) a <> None.
Proof.
  intros rho tp tr ms md mo Bx a HAL Hsp Hin.
  pose proof K18S1_facts as (_ & _ & _ & _ & _ & _ & TB & TL & TH).
  pose proof K18_auxrand as (EAUX & _ & _ & _ & _ & _ & H432 & H464 & HFACT).
  pose proof (U_AUXV18 rho HAL) as UA.
  pose proof HAL as (L1 & L2 & L3 & L5 & L4 & L6 & L7 & L8).
  pose proof (urange (rw rho 1%positive)). pose proof (urange (rw rho 2%positive)). pose proof (urange (rw rho 3%positive)).
  pose proof (urange a). pose proof (urange (eval rho AUXV18)).
  destruct Hsp as [(Hsm & _) _]. rewrite virt_unfold in Hsm.
  pose proof Hsm as (WF & _ & _ & _ & ROM & _). cbn [snd cfg_ms cfg_model] in ROM.
  pose proof (proj1 (smatch_mm segsA _ _ _ _ _ Hsm)) as HOL.
  pose proof (smatch_facts segsA _ _ _ Hsm) as HF.
  change (ax_S (K18r true)) with (K18Sr true) in HOL, WF, HF.
  assert (HLO : 140735340871680 <= bv_unsigned (eval rho AUXV18)).
  { apply existsb_exists in HFACT as (g & Hg & He). apply sprop_eqb_sound in He. subst g.
    pose proof (proj1 (Forall_forall _ _) HF _ Hg) as X. cbn [holds eval] in X.
    rewrite Z_to_bv_unsigned in X. rewrite bv_wrap_small in X by (change (bv_modulus 64) with (2 ^ 64); lia). exact X. }
  destruct Hin as (o & [<-|[]] & Ha1 & Ha2).
  unfold obj_range, obj_lo_of, obj_hi_of in Ha1, Ha2. rewrite TB, TL, TH in Ha1, Ha2.
  unfold MID18 in Ha1, Ha2. rewrite H432 in Ha1, Ha2. rewrite H464 in Ha1, Ha2.
  cbn [fst snd] in Ha1, Ha2. rewrite !soff_lit_small in Ha1, Ha2 by lia.
  rewrite H464 in EAUX. apply nth_error_In in EAUX.
  pose proof (proj1 (Forall_forall _ _) HOL _ EAUX) as OH.
  unfold swf in WF. apply andb_true_iff in WF as [WF _]. apply andb_true_iff in WF as [_ WFO].
  rewrite forallb_forall in WFO. specialize (WFO _ EAUX).
  destruct (obj_byte_readable segsA rho (vms md tp ms) _ (bv_unsigned a - bv_unsigned (eval rho AUXV18)) (ss_next (K18Sr true)) ROM WFO OH)
    as [b Hb].
  { unfold obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi]. rewrite !soff_lit_small by lia. lia. }
  cbn [ob_base] in Hb.
  replace (bv_unsigned (eval rho AUXV18) + (bv_unsigned a - bv_unsigned (eval rho AUXV18))) with (bv_unsigned a) in Hb by lia.
  rewrite Z_to_bv_bv_unsigned in Hb. unfold rd, ms_read_byte in Hb. intros X.
  rewrite X, ROM, (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA.image_byte_none_A a) in Hb by lia. discriminate.
Qed.

(* The join: [K18] is a weakening of each per-flag exit [K18r r]; the valuation keeps every variable
   below 159, every list, and the memory map on the argument region and below [HMB3].  LPS 727298f3:
   with the launch's head equation ([ARG_HGAP r], B/n1.v), the memory map is present on [ARG_TAIL]
   (B/n1.v): no address when CONFIG_RSEQ is off, the dropped and absorbed auxv tail when it is on. *)
Lemma K18_join : forall (r : bool) (mo : Model) (Bx : Z) (rho : valuation) (tp : list word) (w : world),
  arg_layout rho ->
  bv_unsigned (rw rho 1%positive) mod 16 = 0 -> bv_unsigned (rw rho 6%positive) mod 16 = 0 ->
  ARG_HGAP r rho ->
  SPA segsA (KxA mo Bx) (K18r r) rho tp w ->
  exists rho' : valuation,
    (forall i : positive, (i < 159)%positive -> rw rho' i = rw rho i)
    /\ (forall l : positive, rl rho' l = rl rho l)
    /\ (forall a : word, ARGF rho a \/ bv_unsigned a < HMB3 -> rm rho' a = rm rho a)
    /\ (forall a : word, ARG_TAIL rho a -> rm rho' a <> None)
    /\ SPA segsA (KxA mo Bx) K18 rho' tp w.
Proof.
  intros r mo Bx rho tp w HAL A16 R16 HG Hsp. destruct K18_join_ent as [ENT0 ENT1].
  destruct r.
  - pose proof (tail18_clear rho tp w mo Bx) as TAIL.
    destruct w as [tr [ms md]].
    pose proof K18S1_facts as (ESP & HLT & HSAME & EMV & EOBJ & ESET & _).
    pose proof (SPA_split segsA (KxA mo Bx) rho (K18r true) (aux_at (K18Sr true)) MID18 K18S1s tp _ ESP Hsp) as H1.
    assert (H2 : SPA segsA (KxA mo Bx) (mkAX K18S1m X18 (SLit SHB)) rho tp (tr, {| cfg_ms := ms; cfg_model := md |})).
    { pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.StartGlueC.SPA_move_lastX (KxA mo Bx) rho
                    (ax_setS (K18r true) K18S1s) (Datatypes.S (aux_at (K18Sr true))) tp _
                    ltac:(apply Nat.ltb_lt; exact HLT) HSAME H1) as X.
      change (move_obj_last (ax_S (ax_setS (K18r true) K18S1s)) (Datatypes.S (aux_at (K18Sr true))))
        with (move_obj_last K18S1s (Datatypes.S (aux_at (K18Sr true)))) in X.
      rewrite EMV in X. exact X. }
    pose proof (SPA_unobj segsA (KxA mo Bx) rho (mkAX K18S1m X18 (SLit SHB)) (ss_objs K18S1) [otail18] tp tr ms md
                  EOBJ H2 ltac:(intros X; exact X)) as H3.
    cbv zeta in H3.
    change (set_objs (ax_S (mkAX K18S1m X18 (SLit SHB))) (ss_objs K18S1)) with (set_objs K18S1m (ss_objs K18S1)) in H3.
    rewrite ESET in H3.
    set (rho3 := rho_absorb rho [otail18] (vms md tp ms)) in *.
    pose proof (SPA_entails segsA (KxA mo Bx) 159%positive (mkAX K18S1 X18 (SLit SHB)) K18 [] rho3 tp _
                  ENT1 eq_refl (stableA_KxA segsA 159%positive mo Bx) H3) as H4.
    pose proof (rho_sub_agree [] 159%positive rho3 eq_refl) as (V & Lr & M).
    exists (rho_sub rho3 []). split; [|split; [|split; [|split]]].
    + intros i Hi. rewrite <- (V i Hi). reflexivity.
    + intros l. rewrite <- (Lr l). reflexivity.
    + intros a Ha. rewrite <- (M a). unfold rho3.
      apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA.rm_absorb_outside.
      intros Hin. exact (TAIL a HAL A16 R16 Hsp Hin Ha).
    + intros a Ha. rewrite <- (M a). unfold rho3.
      assert (Hin : in_ranges rho [otail18] a).
      { pose proof K18S1_facts as (_ & _ & _ & _ & _ & _ & TB & TL & TH).
        pose proof K18_auxrand as (_ & _ & _ & _ & _ & _ & H432 & H464 & _).
        pose proof (U_AUXV18 rho HAL) as UA. pose proof (urange a).
        exists otail18. split; [left; reflexivity|]. cbv zeta.
        unfold obj_range, obj_lo_of, obj_hi_of. rewrite TB, TL, TH. unfold MID18. rewrite H432, H464.
        cbn [fst snd]. rewrite !soff_lit_small by lia. rewrite UA.
        unfold ARG_TAIL in Ha. unfold ARG_HGAP in HG.
        change (Z.of_nat (LinuxProcessSemantics.LinuxProcessSem.StackLayout.auxv_size false)) with 432 in Ha.
        change (Z.of_nat (LinuxProcessSemantics.LinuxProcessSem.StackLayout.auxv_size true)) with 464 in HG.
        lia. }
      rewrite (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA.rm_absorb_inside rho [otail18] _ a Hin).
      exact (tail18_present rho tp tr ms md mo Bx a HAL Hsp Hin).
    + exact H4.
  - pose proof (SPA_entails segsA (KxA mo Bx) 159%positive (K18r false) K18 [] rho tp w
                  ENT0 eq_refl (stableA_KxA segsA 159%positive mo Bx) Hsp) as H4.
    pose proof (rho_sub_agree [] 159%positive rho eq_refl) as (V & Lr & M).
    exists (rho_sub rho []). split; [|split; [|split; [|split]]].
    + intros i Hi. symmetry. exact (V i Hi).
    + intros l. symmetry. exact (Lr l).
    + intros a _. symmetry. exact (M a).
    + intros a Ha. exfalso. unfold ARG_TAIL in Ha. unfold ARG_HGAP in HG.
      change (Z.of_nat (LinuxProcessSemantics.LinuxProcessSem.StackLayout.auxv_size false)) with 432 in Ha, HG.
      lia.
    + exact H4.
Qed.
