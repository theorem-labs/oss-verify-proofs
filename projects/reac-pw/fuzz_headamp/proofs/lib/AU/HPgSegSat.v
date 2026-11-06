(* The T0.6 witness of lib/AU/HPgSeg.v at reac-pw/fuzz_headamp's image B: the premises that file's statements
   carry are satisfiable at this unit's real instance, the record HPgImgB.headamp_himg_B and the builder's pcs
   HPgSeg.headamp_bld_B. HPgSeg.v Requires no image module (it takes the record and the pcs as Section variables),
   so the witness lives here, beside it, as lib/AU/HPgSatU.v lives beside the contracts.
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgImgB HPgSeg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* The 29 pcs the builder's cut states and continuations name, as one list: the two arms of the shape test and
   their join, the property loop's head, the four ends of one property's selector and key, the pod loop's head,
   ent_build's nine table entries and its three other entries, the pod loop's close, the latch, the builder's two
   ends, and the corruption's head and tail. *)
Definition headamp_bld_B_pcs : list Z :=
[bi_B7 headamp_bld_B; bi_BO headamp_bld_B; bi_PH headamp_bld_B;
 bi_N headamp_bld_B; bi_SEL7 headamp_bld_B; bi_SELK headamp_bld_B; bi_SELI headamp_bld_B;
 bi_SELS headamp_bld_B; bi_C headamp_bld_B; bi_d9 headamp_bld_B; bi_D0E headamp_bld_B;
 bi_G headamp_bld_B; bi_J headamp_bld_B; bi_CL headamp_bld_B; bi_LATCH headamp_bld_B;
 bi_P headamp_bld_B; bi_P1 headamp_bld_B; bi_R headamp_bld_B; bi_RT headamp_bld_B]
++ bi_dt headamp_bld_B.
(* a pc of LLVMFuzzerTestOneInput (0x80c40, 12860 bytes, so [0x80c40, 0x83a1c)), 4-aligned *)
Definition hsu_pc_ok (a : Z) : bool := (0x80c40 <=? a) && (a <? 0x83a1c) && (a mod 4 =? 0).

(* Image B's prologue pattern has 116 granules, so the two states the builder makes have 116 too and the three
   granule windows it opens (t 4..15, ch 20..22, e62 66..78) lie inside them; the 28 pcs are distinct instruction
   addresses of the entry function; and the builder's two segment cuts are the record's own C1 and C2, the pcs
   HPgSeg's piece statements use through hi_c1 and hi_c2. *)
Lemma headamp_bld_B_sat :
length (hsu_P0 headamp_himg_B) = 116%nat /\
length (hsu_PJ headamp_himg_B) = 116%nat /\
length (hsu_PG headamp_himg_B) = 116%nat /\
hsu_nodupb headamp_bld_B_pcs = true /\
forallb hsu_pc_ok headamp_bld_B_pcs = true /\
hi_c1 headamp_himg_B = 0x80fcc /\ hi_c2 headamp_himg_B = 0x82efc /\
(forall i, (66 <= i < 79)%nat -> nth i (hsu_PJ headamp_himg_B) 0 = 0) /\
(forall i, ((4 <= i < 16)%nat \/ (20 <= i < 23)%nat \/ (66 <= i < 79)%nat) ->
 nth i (hsu_PG headamp_himg_B) 0 = 0).
Proof.
assert (L0 : length (hsu_P0 headamp_himg_B) = 116%nat) by (vm_compute; reflexivity).
assert (LJ : length (hsu_PJ headamp_himg_B) = 116%nat)
  by (unfold hsu_PJ; rewrite hsu_open_length; exact L0).
assert (LG : length (hsu_PG headamp_himg_B) = 116%nat)
  by (unfold hsu_PG; rewrite !hsu_open_length; exact L0).
split; [exact L0|]. split; [exact LJ|]. split; [exact LG|].
split; [vm_compute; reflexivity|].
split; [vm_compute; reflexivity|].
split; [reflexivity|]. split; [reflexivity|].
split.
- intros i Hw. apply hsu_PJ_in; [exact Hw | rewrite L0; lia].
- intros i Hw. apply hsu_PG_in; [exact Hw | rewrite L0; lia].
Qed.

(* The write set the builder's cuts use, hi_w1, covers every real-frame cell and every frame object those cuts
   name: the cells run to R+0x158 and the objects to F + 0x210 + 104, and hi_w1's ranges are [F+0x20, F+0x278),
   the 116 shadow bytes of the frame, and [R, R+0x198). *)
Lemma headamp_bld_B_w1 : hi_w1 headamp_himg_B = [(XF 0, 0x20, 0x258); (XShF, 0, 116); (XR, 0, 0x198)].
Proof. reflexivity. Qed.
Lemma headamp_bld_B_w1_covers : forall (e : hd_env),
(forall o, 0 <= o <= 0x158 -> hd_inw e (hi_w1 headamp_himg_B) (e_R e + o)) /\
(forall c, 0x20 <= c < 0x278 -> hd_inw e (hi_w1 headamp_himg_B) (e_F e + c)).
Proof.
intros e. split.
- intros o Ho. rewrite headamp_bld_B_w1. apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd.
  cbn [fst snd hd_xv]. lia.
- intros c Hc. rewrite headamp_bld_B_w1. apply Exists_cons_hd. cbn [fst snd hd_xv]. lia.
Qed.

(* The pod field offsets HPgSeg.v's cut lists write as numerals are the shared model's: the builder reads the
   length cell at pp + OFF_LEN and the five header words after it, writes the corrupt word at pp + OFF_CORRUPT,
   and its capacity guards compare against POD_BUF_MAX. *)
Lemma hsu_pod_offsets :
Layout.OFF_LEN = 0x4000 /\ Layout.OFF_IS_PROPS = 0x4008 /\ Layout.OFF_HAS_PARAMS = 0x400c /\
Layout.OFF_PARAMS_STRUCT = 0x4010 /\ Layout.OFF_ENT = 0x4014 /\ Layout.OFF_N_ENT = 0x4d14 /\
Layout.OFF_CORRUPT = 0x4d18 /\ Layout.PP_SIZE = 0x4d20 /\ Layout.POD_BUF_MAX = 0x4000.
Proof. repeat split. Qed.

Print Assumptions headamp_bld_B_sat.
Print Assumptions headamp_bld_B_w1.
Print Assumptions headamp_bld_B_w1_covers.
Print Assumptions hsu_pod_offsets.
(* the proved lemmas of lib/AU/HPgSeg.v *)
Print Assumptions hsu_granules_of_offsets.
Print Assumptions hsu_open_length.
Print Assumptions hsu_open_nth.
Print Assumptions hsu_open_in.
Print Assumptions hsu_open_out.
Print Assumptions hsu_cut_lists_nodup.
Print Assumptions hsu_patterns_len.
Print Assumptions hsu_PJ_in.
Print Assumptions hsu_PJ_out.
Print Assumptions hsu_PG_in.
Print Assumptions hsu_PG_out.
