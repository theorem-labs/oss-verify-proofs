(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file for fuzz_ctrl image A (asan); owner a Theorem Labs lane. *)
(* lib/A/ACtlGlobs.v -- fuzz_ctrl image A (libreac v1.9.0, ASan build): the registered-globals list GLOBS_A of the top
   composition lib/A/ACtl.v (Section Ctl, :317-321 at a working branch bb5910bdb23) and its two
   premises, proved as closed lemmas.
   proves no function (kind: start-up facts) -- image-A registered-globals facts; no function is walked.

   - ctrl_globs_A: the image's registered-globals list, all 57 descriptors of its asan_globals table, in table order,
     each as (beg, size) with the registered size (never size_with_redzone).
   - ctrl_globs_A_marked_B: for every asyms B with A.AF0m.CtrlTSyms B, A.Prog.CtrlRo.globs_marked tfibsegs B
     ctrl_globs_A (ACtl.v:318's GLOBS_A_MARKED with GLOBS_A := ctrl_globs_A, at Section Ctl's Variable B and its
     TFIB_SYMS); ctrl_globs_A_marked: the same at the top's B := A.AD2l.CtrlB, through A.AD2l.CtrlB_syms.
   - ctrl_name_glob_A: ACtl.v:321's NAME_GLOB with GLOBS_A := ctrl_globs_A, verbatim otherwise.
   - ctrl_globs_A_sw / ctrl_globs_A_cat: the switch table (0x21980, 56) and the catalogue (0x9e800, 3256) are rows
     (ACtl.v:317-318: a Theorem Labs lane's pb_ needs both in the list).

   PROVENANCE
   - RULE 24 (released proofs first): second-agent lookup by a Theorem Labs lane (run for a Theorem Labs lane, 2026-10-29 17:2xZ) CONFIRM:
     proof-index globs_marked / GLOBS_A_MARKED / NAME_GLOB / ctl_global_shadow_of_AR / ctl_gshadow_of_AR has 0
     released hits and no fuzz_ctrl-A proof on any working-branch ref; ProgWorldShadow's ctl_global_shadow_of_AR /
     ctl_gshadow_of_AR conclude AsanRT.addressable, not block_shadow, so globs_marked does not follow from them.
   - template (same unit, image B): lib/B/ProgBridgeData.v at a working branch 51de8d2c1ffe: its
     bd_cell_sh / bd_cell_sh_eq / bd_le_byte_small (:146-185), bd_sh_val_ok / bd_glob_marked_ok /
     bd_globs_marked_ok (:398-414), bd_row_glob_ok / bd_rows_glob_ok (:452-460), bd_sh_val (:870) and
     ctrl_ro_globs_marked (:907), with B's generated tables (lib/Reusable/YF0m.v) replaced by image A's (A.AF0m:
     Tfib_zero_shadow :2955, Tfib_const_shadow :2167, Tfib_const :2954, CtrlTSyms :2986, ts_const :3002, ts_zsh
     :3006) and ctl_names_ro's unpacking (:1005) restated for NAME_GLOB's conclusion.  No lib/B file is Required.

   THE LIST (generated, never typed): lib/A/ctrl_globs_A.py (sha256 221418630ee6e5c2991798589f9ede097358bb0b287032d9950479f9daaf8b8a)
   decodes AsanRT.v's RT_AGLOB_Z (the asan_globals bytes the core carries at RT_AGLOB = 0xa4380, RT_AGLOB_LEN = 3648;
   AsanRT.v blob b67d26f8ec71 (the blob this tree had at release c5e779efe8c) on bb5910bdb23) as 57 '<8Q' descriptors and prints (beg, size) = fields 0 and 1.  Its
   self-test runs every invocation (6 known-answer cases: 57 descriptors / 3648 bytes, entries 0 / 51 / 54 / 55 / 56,
   and EMPTY, TRUNCATED and two MUTATED tables rejected; exit 2 if any moves).  Command, from lib/:
     python3 A/ctrl_globs_A.py A/AsanRT.v fuzz_ctrl.nm.txt (a working note, not in this delivery)
   Its full output is lib/A/ctrl_globs_A.txt (a working note, not in this delivery) (sha256 9b40e4fbfb57f0574f8e0593533c9c2656777aa8a36b52a84fad47a1adb9b122);
   the Definition below is that output's last 11 lines, verbatim.  The nm.txt (the pin's unstripped twin's symbol table,
   sha256 b81ffc37932b) only names the rows in the output's comments.

   ENTRY 54 (KIND_NAME, beg 0x9e760, size 0x70) IS KEPT: image A's runtime registers it.  Image B's list
   (ctrl_ro_globs) leaves out the descriptor at the same position; image A's keeps every descriptor, because the
   module constructor registers the whole table.  Measured (neutral_dis.py a7ea7c9ea80d over
   libreac-v190/asan/fuzz_ctrl, the unstripped twin 78efaeda1de5 of the pin aac16e1fe728):
     asan.module_ctor 0x83150: a1 := ld [0xa0748], a2 := ld [0xa0750], a0 := 0xa51c0, jal 0x40898
       (__asan_register_elf_globals, rt_3 in the excerpt);
     0x40898: returns if a1 = a2 or [a0] <> 0; else a2 := (a2 - a1) >> 6, call 0x3f4b0 (__asan_register_globals)
       with (a1, a2), then [a0] := 1.
   The core's start-up cells give the operands: Tfib_const_abs (AF0m.v:113-115) pins [0xa0748] = 0xa4380 (= RT_AGLOB,
   __start_asan_globals), [0xa0750] = 0xa51c0 (= RT_AGLOB + RT_AGLOB_LEN, __stop_asan_globals) and the flag
   [0xa51c0] = 1 (registration done), so the count is 3648 >> 6 = 57: entries 0 .. 56, entry 54 among them.  The
   record's shadow agrees: Tfib_zero_shadow's range (0x21aa0, 0x9e7d0 - 0x21aa0) ends at KIND_NAME's end, and its
   redzone [0x9e7d0, 0x9e800) has the poison cells 0x8000bcfa .. 0x8000bcff := 0xf9 in Tfib_const_shadow (a
   registered global's redzone); ctrl_globs_A_marked decides KIND_NAME's 14 shadow bytes = 0 with the other rows.

   No Axiom, no Parameter, no Admitted. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* YK11 and YM05 have twins under lib/A, lib/B and lib/U: Required and named by their full CORE path. *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YA0n YG0f YG0v YG0n YG0d YG0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v AF0m AD2l.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require CtrlRo SlotModel.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.
Import ListNotations.
Local Open Scope Z_scope.

Local Notation segs := A.AB1v.tfibsegs.

(* ---- The list: generated by lib/A/ctrl_globs_A.py (output lib/A/ctrl_globs_A.txt); entries 0 .. 56 in table order. ---- *)

Definition ctrl_globs_A : list (Z * Z) :=
  [ (0x21140, 0x6); (0x21160, 0x1); (0x21180, 0xc); (0x211e0, 0x2); (0x21200, 0x7); (0x21220, 0x5);
    (0x21240, 0x7); (0x21260, 0xf); (0x21280, 0xa); (0x212a0, 0x10); (0x212c0, 0x6); (0x212e0, 0x8);
    (0x21300, 0x7); (0x21320, 0xf); (0x21340, 0x10); (0x21360, 0xa); (0x21380, 0x10); (0x213a0, 0x6);
    (0x213c0, 0xd); (0x213e0, 0x6); (0x21400, 0x17); (0x21440, 0x6); (0x21460, 0x16); (0x214a0, 0x7);
    (0x214c0, 0x7); (0x214e0, 0x1d); (0x21520, 0xc); (0x21540, 0x1d); (0x21580, 0x6); (0x215a0, 0x17);
    (0x215e0, 0x8); (0x21600, 0x6); (0x21620, 0x18); (0x21660, 0x8); (0x21680, 0x7); (0x216a0, 0x18);
    (0x216e0, 0x9); (0x21700, 0x7); (0x21720, 0x18); (0x21760, 0x9); (0x21780, 0x7); (0x217a0, 0x17);
    (0x217e0, 0x8); (0x21800, 0x7); (0x21820, 0x17); (0x21860, 0x8); (0x21880, 0x7); (0x218a0, 0x18);
    (0x218e0, 0x8); (0x21900, 0x20); (0x21940, 0x20); (0x21980, 0x38); (0x21a20, 0x20); (0x21a60, 0x20);
    (0x9e760, 0x70); (0x9e800, 0xcb8); (0x9f7e0, 0x108) ].

Lemma ctrl_globs_A_length : length ctrl_globs_A = 57%nat.
Proof. reflexivity. Qed.

(* The switch table (entry 51) and BOX_CATALOGUE (entry 55) are rows. *)
Lemma ctrl_globs_A_sw : In (0x21980, 56) ctrl_globs_A.
Proof. unfold ctrl_globs_A. do 51 right. left. reflexivity. Qed.

Lemma ctrl_globs_A_cat : In (0x9e800, 3256) ctrl_globs_A.
Proof. unfold ctrl_globs_A. do 55 right. left. reflexivity. Qed.

(* ---- Closed checkers over image A's generated tables (A.AF0m), decided by vm_compute. ---- *)

(* A one-byte constant cell (ANum s) := k of the core's cell list. *)
Definition ag_cell_sh (c : Reusable.YG0f.acell) : option (Z * Z) :=
  match c with
  | Reusable.YG0f.ACell (Reusable.YG0f.ANum s) 1 (Reusable.YG0f.AV (Reusable.YG0f.ANum k)) => Some (s, k)
  | _ => None
  end.

Lemma ag_cell_sh_eq : forall c s k, ag_cell_sh c = Some (s, k) ->
  c = Reusable.YG0f.ACell (Reusable.YG0f.ANum s) 1 (Reusable.YG0f.AV (Reusable.YG0f.ANum k)).
Proof.
  intros [ca cw cv] s k H. destruct ca; try (cbn in H; discriminate H).
  destruct cw as [|[|cw]]; try (cbn in H; discriminate H).
  destruct cv as [e|mask v]; try (cbn in H; discriminate H).
  destruct e; try (cbn in H; discriminate H).
  cbn in H. injection H as -> ->. reflexivity.
Qed.

Lemma ag_le_byte_small : forall k, 0 <= k < 256 -> Reusable.YG0f.le_byte k 1 0 = k.
Proof.
  intros k Hk. unfold Reusable.YG0f.le_byte.
  change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  change (2 ^ 8) with 256. rewrite (Z.mod_small k 256) by lia. rewrite (Z.mod_small k 256) by lia. reflexivity.
Qed.

(* Shadow byte s holds v at every AR state: v = 0 and s is a full-granule shadow byte of a Tfib_zero_shadow range,
   or Tfib_const_shadow has the one-byte cell (s, v). *)
Definition ag_sh_val_ok (s v : Z) : bool :=
  (if v =? 0 then
     existsb (fun r => (Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF (fst r) <=? s) &&
                       (s <? Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF (fst r) + snd r / 8))
       A.AF0m.Tfib_zero_shadow
   else false) ||
  existsb (fun c => match ag_cell_sh c with
                    | Some (s0, k) => (s0 =? s) && (k =? v) && (0 <=? k) && (k <? 256)
                    | None => false
                    end) A.AF0m.Tfib_const_shadow.

(* (q, sz) is block_shadow-marked: 8-aligned, and each granule's shadow byte is 0, the last partial one sz mod 8. *)
Definition ag_glob_marked_ok (g : Z * Z) : bool :=
  let (q, sz) := g in
  (q mod 8 =? 0) && (0 <=? sz) &&
  forallb (fun i => ag_sh_val_ok (Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF q + Z.of_nat i)
                                 (if Z.of_nat i <? sz / 8 then 0 else sz mod 8))
          (seq 0 (Z.to_nat ((sz + 7) / 8))).

Lemma ag_globs_marked_ok : forallb ag_glob_marked_ok ctrl_globs_A = true.
Proof. vm_compute. reflexivity. Qed.

(* Row i of BOX_CATALOGUE: no name, or a name (its C string with the NUL, img_cstr) inside one row of ctrl_globs_A. *)
Definition ag_row_glob_ok (i : nat) : bool :=
  let row := A.Prog.SlotModel.rowb (Z.of_nat i) in
  let p := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.rname row in
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.has row =? 0) || (p =? 0) ||
  existsb (fun g : Z * Z => (fst g <=? p) &&
                            (p + Z.of_nat (length (A.Prog.SlotModel.img_cstr p 16)) <=? fst g + snd g)) ctrl_globs_A.

Lemma ag_rows_glob_ok : forallb ag_row_glob_ok (seq 0 11) = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- NAME_GLOB (ACtl.v:321) at GLOBS_A := ctrl_globs_A. ---- *)

Theorem ctrl_name_glob_A : forall i, 0 <= i < 11 -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.has (A.Prog.SlotModel.rowb i) <> 0 -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.rname (A.Prog.SlotModel.rowb i) <> 0 -> exists q sz, In (q, sz) ctrl_globs_A /\ q <= OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.rname (A.Prog.SlotModel.rowb i) /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.rname (A.Prog.SlotModel.rowb i) + Z.of_nat (length (A.Prog.SlotModel.img_cstr (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.rname (A.Prog.SlotModel.rowb i)) 16)) <= q + sz.
Proof.
  intros i Hi Hhas Hname.
  assert (Hin : In (Z.to_nat i) (seq 0 11)) by (apply in_seq; lia).
  pose proof (proj1 (forallb_forall ag_row_glob_ok (seq 0 11)) ag_rows_glob_ok _ Hin) as Hr.
  unfold ag_row_glob_ok in Hr. cbv zeta in Hr. rewrite Z2Nat.id in Hr by lia.
  apply orb_prop in Hr as [Hr | Hr]; [apply orb_prop in Hr as [Hr | Hr]|].
  - apply Z.eqb_eq in Hr. contradiction.
  - apply Z.eqb_eq in Hr. contradiction.
  - apply existsb_exists in Hr as ([q sz] & Hg & Hb). cbn [fst snd] in Hb.
    apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    exists q, sz. split; [exact Hg|]. split; [exact H1 | exact H2].
Qed.

(* ---- GLOBS_A_MARKED (ACtl.v:318): for every B whose tables are image A's generated ones. ---- *)

Section GlobsA.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}.
Variable B : Reusable.YG0f.asyms.
(* B's tables are image A's generated ones (the core's CtrlTSyms record; ACtl.v's TFIB_SYMS). *)
Hypothesis HB : A.AF0m.CtrlTSyms B.

(* An ag_sh_val_ok shadow byte holds its value at every AR state. *)
Lemma ag_sh_val : forall ly S (W : Reusable.YA0n.world segs) (mem : word -> option byte) md s v,
  Reusable.YG0n.AR segs B ly S W mem md -> ag_sh_val_ok s v = true ->
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem s = Some v.
Proof.
  intros ly S W mem md s v HAR Hok. unfold ag_sh_val_ok in Hok.
  apply orb_prop in Hok as [Hz | Hc].
  - destruct (Z.eqb_spec v 0) as [Hv|Hv]; [|discriminate Hz]. subst v.
    apply existsb_exists in Hz as (r & Hr & Hb).
    apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    pose proof (Reusable.YG0d.al_zshadow _ _ (Reusable.YG0q.AR_laws_ok segs B) ly S W mem md r HAR) as Hzs.
    specialize (Hzs ltac:(unfold Reusable.YG0n.zero_shadow_ranges; right;
                          rewrite (A.AF0m.ts_zsh B HB); exact Hr)).
    specialize (Hzs (s - Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF (fst r)) ltac:(lia)).
    replace (Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF (fst r) +
             (s - Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF (fst r))) with s in Hzs by lia.
    exact Hzs.
  - apply existsb_exists in Hc as (c & Hin & Hc).
    destruct (ag_cell_sh c) as [[s0 k]|] eqn:Hcs; [|discriminate Hc].
    apply andb_prop in Hc as [Hc H4]. apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
    apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.leb_le in H3. apply Z.ltb_lt in H4.
    apply ag_cell_sh_eq in Hcs. subst c s0 k.
    pose proof (Reusable.YG0n.am_const _ _ _ _ (proj1 HAR)) as HC.
    rewrite (A.AF0m.ts_const B HB ly) in HC. rewrite Forall_forall in HC.
    assert (Hin' : In (Reusable.YG0f.ACell (Reusable.YG0f.ANum s) 1 (Reusable.YG0f.AV (Reusable.YG0f.ANum v)))
                      (A.AF0m.Tfib_const ly)).
    { unfold A.AF0m.Tfib_const. apply in_or_app. right. apply in_or_app. right. exact Hin. }
    specialize (HC _ Hin'). unfold Reusable.YG0f.cell_holds in HC.
    cbn [Reusable.YG0f.aeval Reusable.YG0f.c_at Reusable.YG0f.c_val Reusable.YG0f.c_w] in HC.
    specialize (HC 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in HC. rewrite Z.add_0_r in HC.
    rewrite (ag_le_byte_small v ltac:(lia)) in HC. exact HC.
Qed.

Theorem ctrl_globs_A_marked_B : A.Prog.CtrlRo.globs_marked segs B ctrl_globs_A.
Proof.
  intros ly S W mem md q sz Hin HAR.
  pose proof (proj1 (forallb_forall _ _) ag_globs_marked_ok _ Hin) as Hg.
  unfold ag_glob_marked_ok in Hg. cbn beta iota in Hg.
  apply andb_prop in Hg as [Hg Hall]. apply andb_prop in Hg as [Hq Hsz].
  apply Z.eqb_eq in Hq. apply Z.leb_le in Hsz. rewrite forallb_forall in Hall.
  unfold Reusable.YG0v.block_shadow. split; [exact Hq|]. split; [exact Hsz|].
  intros i Hi.
  assert (Hn : In (Z.to_nat i) (seq 0 (Z.to_nat ((sz + 7) / 8)))) by (apply in_seq; lia).
  specialize (Hall _ Hn). rewrite Z2Nat.id in Hall by lia.
  exact (ag_sh_val ly S W mem md _ _ HAR Hall).
Qed.

End GlobsA.

(* ---- GLOBS_A_MARKED at the top's B := A.AD2l.CtrlB (ACtl.v section 9). ---- *)

Section GlobsATop.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}.

Theorem ctrl_globs_A_marked : A.Prog.CtrlRo.globs_marked segs A.AD2l.CtrlB ctrl_globs_A.
Proof. exact (ctrl_globs_A_marked_B A.AD2l.CtrlB A.AD2l.CtrlB_syms). Qed.

End GlobsATop.
