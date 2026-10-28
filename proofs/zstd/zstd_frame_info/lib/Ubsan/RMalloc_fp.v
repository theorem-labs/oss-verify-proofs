(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Export Malloc_fp.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import ProgDeps.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RMallocRep RMallocTree RF_enframe RMallocKit_A.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Notation RMFACTS := (@MFACTS_g _ ref_reserved).

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma rreserved_disjoint2 : forall b n, ranges_free ref_reserved b n = true -> 0 < n ->
  (b + n <= 0x10000 \/ 0x1c000 <= b) /\ (b + n <= 0x1c000 \/ 0x4f000 <= b).
Proof. intros b n H Hn. pose proof (rreserved_disjoint b n H). Local Ltac2 Set LiaHints.tbl := fun () => "0010=59264726735.6000007S2Hn2H0".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma wr8_comm p q v w st : fst p = fst q -> snd p <> snd q -> wr8 p v (wr8 q w st) = wr8 q w (wr8 p v st).
Proof.
  intros Hf Hs.
  assert (E : forall (a b : aptr) x y s, fst a = fst b -> snd a <> snd b ->
     wr8 a x (wr8 b y s) = set_shadow (<[fst a := mkShadow (<[snd a := (Z.land x 255, s_tick s)]> (<[snd b := (Z.land y 255, s_tick s)]> (r_cells (get_shadow s (fst a))))) (r_hav (get_shadow s (fst a))) (r_havp (get_shadow s (fst a)))]> (s_shadow s)) s).
  { intros a b x y s Ef Ns. unfold wr8 at 1. unfold upd_shadow. rewrite Ef, get_shadow_wr8_same. cbn [r_cells r_hav r_havp].
    rewrite s_shadow_wr8, <- Ef. change (s_tick (wr8 b y s)) with (s_tick s). rewrite insert_insert_eq. reflexivity. }
  rewrite (E p q), (E q p) by (congruence || (symmetry; congruence) || auto). rewrite Hf.
  rewrite (insert_insert_ne _ (snd p) (snd q)) by exact Hs. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Section ENFRAME.
Variables (st2 : mstate) (m4 : mem) (g b : aptr) (r : region) (k n off : Z).
Let mr := get_meta_rec st2 g.
Let stride := get_stride mr.
Let B := conc st2 b.
Let P0 := B + 16 + stride * k.

Hypothesis MR : rmrep st2 m4.
Hypothesis TK : ticks_ok st2.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hr : (s_regions st2) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis K0 : 0 <= k < 32.
Hypothesis SPAN : snd b + 16 + stride * (k + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis S31 : stride - 4 - n < 2^31.
Hypothesis NOGRP : forall b' gh, (s_groups st2) !! b' = Some gh -> fst b' = fst b ->
  snd b' + 9 <= snd b + 16 + stride * k - 4 \/ snd b + 16 + stride * k + stride - 4 <= snd b'.
Hypothesis OFF0 : 0 <= off.
Hypothesis N0 : 0 <= n.
Hypothesis FIT : 16 * off + n + 4 <= stride.
Hypothesis Q16 : (stride * k + 16 * off) / 16 < 65536.

#[using="Hr"] Lemma rconc_b : B = r_base r + snd b.
Proof. unfold B. apply (conc_region' st2 b r Hr). Qed.

#[using="b off B P0 K0 S16"] Lemma rsk_nonneg : 0 <= stride * k.
Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0020>18588176547.2851792621753.2800000800<S2K03S16S2K0".
apply Z.mul_nonneg_nonneg; lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="off B P0 Hr Hk B0 K0 SPAN S16 NOGRP"] Lemma rwr8_rep : forall stx mx (o v : Z),
  rmrep stx mx -> ticks_ok stx ->
  s_regions stx = s_regions st2 -> s_groups stx = s_groups st2 ->
  snd b + 16 + stride * k - 4 <= o < snd b + 16 + stride * k + stride - 4 ->
  0 <= v < 256 ->
  rmrep (wr8 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) [b8 v]) /\ ticks_ok (wr8 (fst b, o) v stx).
Proof.
  intros stx mx o v MRx TKx ER EG Ho Hv. pose proof rsk_nonneg.
  split; [|apply ticks_ok_wr8; exact TKx].
  Local Ltac2 Set LiaHints.tbl := fun () => "0020>10336122861.4446170967393.3900000=00NS2K02Ho2Hf2H0S2B02K04SPAN2Ho1H".
apply (rmrep_wr8 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| |exact Hv].
  intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="off B P0 Hr Hk B0 K0 SPAN S16 NOGRP"] Lemma rwr16_rep : forall stx mx (o v : Z),
  rmrep stx mx -> ticks_ok stx ->
  s_regions stx = s_regions st2 -> s_groups stx = s_groups st2 ->
  snd b + 16 + stride * k - 4 <= o -> o + 2 <= snd b + 16 + stride * k + stride - 4 ->
  0 <= v < 65536 ->
  rmrep (wr16 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) (le2 (wz v))) /\ ticks_ok (wr16 (fst b, o) v stx).
Proof.
  intros stx mx o v MRx TKx ER EG Ho Ho2 Hv. pose proof rsk_nonneg.
  split; [|apply ticks_ok_wr16; exact TKx].
  Local Ltac2 Set LiaHints.tbl := fun () => "0030>62034908776.4064362796846.458943377619.40 00000=00N00ZS2K04SPAN3Ho2S2K02Ho2Hf2H03Ho2S2B02K02Ho1H".
apply (rmrep_wr16 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| lia| |exact Hv].
  intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="off B P0 Hr Hk B0 K0 SPAN S16 NOGRP"] Lemma rwr32_rep : forall stx mx (o v : Z),
  rmrep stx mx -> ticks_ok stx ->
  s_regions stx = s_regions st2 -> s_groups stx = s_groups st2 ->
  snd b + 16 + stride * k - 4 <= o -> o + 4 <= snd b + 16 + stride * k + stride - 4 ->
  0 <= v < 2^32 ->
  rmrep (wr32 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) (le4 (wz v))) /\ ticks_ok (wr32 (fst b, o) v stx).
Proof.
  intros stx mx o v MRx TKx ER EG Ho Ho4 Hv. pose proof rsk_nonneg.
  Local Ltac2 Set LiaHints.tbl := fun () => "0030>28745634254.4545564601928.408943377619.40 00000A00N00ZS2K02Ho2Hf2H03Ho4S2K04SPAN3Ho4S2B02K02Ho1H".
apply (rmrep_wr32 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| lia| |exact Hv].
  intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="st2 g b k off mr stride B P0 K0"] Lemma wr16_wr8_comm p q v w st : fst p = fst q -> snd q <> snd p -> snd q <> snd p + 1 ->
  wr8 q w (wr16 p v st) = wr16 p v (wr8 q w st).
Proof.
  intros Hf H0 H1. unfold wr16.
  Local Ltac2 Set LiaHints.tbl := fun () => "0020>66153604003.369307245548.36 00000=00DS2K02Hf2H02H1S2K02Hf".
rewrite (wr8_comm q (aadd p 1)) by (unfold aadd; cbn; lia || auto).
  rewrite (wr8_comm q p) by (auto || lia). reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="st2 g b k off mr stride B P0 K0"] Lemma wr32_wr8_comm p q v w st : fst p = fst q -> snd q + 1 = snd p ->
  wr8 q w (wr32 p v st) = wr32 p v (wr8 q w st).
Proof.
  intros Hf H1. unfold wr32.
  Local Ltac2 Set LiaHints.tbl := fun () => "0050>2457154115.35 51950852914.3557151117299.3566153604003.359307245548.35 00000:00D00N00X00_S2K02Hf2H1S2K02Hf2H1S2K02Hf2H1S2K02Hf2H1S2K02Hf".
rewrite (wr8_comm q (aadd p 3)) by (unfold aadd; cbn; lia || auto).
  rewrite (wr8_comm q (aadd p 2)) by (unfold aadd; cbn; lia || auto).
  rewrite (wr8_comm q (aadd p 1)) by (unfold aadd; cbn; lia || auto).
  rewrite (wr8_comm q p) by (auto || lia). reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="r MR TK Hmem Hr Hk B0 K0 SPAN S16 S31 NOGRP OFF0 N0 FIT Q16"] Lemma renframe_mrep :
  let res := enframe_at st2 g k n off in
  rmrep (fst res) (renframe_tail_mem (renframe_off_mem m4 P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
  /\ ticks_ok (fst res)
  /\ conc st2 (snd res) = P0 + 16 * off /\ fst (snd res) = fst b /\ snd (snd res) = snd b + 16 + stride * k + 16 * off.
Proof.
  pose proof rconc_b as CB. pose proof rsk_nonneg as SK.
  cbv zeta. unfold enframe_at. fold mr. fold stride. rewrite Hmem. cbn [default from_option id fst snd].
  unfold aadd. cbn [fst snd].
  (* [comment removed for export] *)
  set (stC := if negb (off =? 0) then _ else _).
  assert (PRE : rmrep (fst stC) (renframe_off_mem m4 P0 off) /\ ticks_ok (fst stC)
                /\ snd stC = (fst b, snd b + (UNIT + stride * k) + UNIT * off)
                /\ s_regions (fst stC) = s_regions st2 /\ s_groups (fst stC) = s_groups st2
                /\ (forall q, conc (fst stC) q = conc st2 q)).
  { subst stC. unfold renframe_off_mem. destruct (Z.eqb_spec off 0) as [E|NE]; cbn [negb fst snd].
    - subst off. rewrite Z.mul_0_r, Z.add_0_r.
      split; [exact MR|]. split; [exact TK|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros; reflexivity.
    - (* [comment removed for export] *)
      Local Ltac2 Set LiaHints.tbl := fun () => "00c0>10908052872.3312523728919.3913573381461.3513914994076.4615868994903.4016224964385.3716365402129.311687920188.48 17939814727.4217939817200.3320389260129.3722161312990.3822671763568.562359842792.44 24486973918.6427465610844.3128153479485.4029315430951.6132886679841.3733066566632.4233066580063.3333549961934.5035459439440.5839131325723.4240040186195.6140134639569.5645386294671.3145437569413.4045437731729.6245437782784.3146062788656.3751118273987.6251792416230.6154254711694.405512517439.56 55763663808.5455996951438.3956606127779.5457020063676.5457020096444.4857020458249.355894134728.44 59087287440.586181677823.54 62625299421.3162625332189.5462625544536.406440626553.58 65502243693.3967710181982.457222656071.61 00000@00D00[01401801?01C01h02A02I02P02T02X02h02l03003403803?03O03S03j04>04E04I04U04Y05705U05]05d06@06D06H06P06X06k06o07307707;07K07_07j07n08208608:08>08B08FS2K04OFF03Q162SKS2K0S2K03S164OFF02N03FIT2SKS2K04OFF03FIT2CB3Epo4ErsvS2K0S2K02CBS2K0S2K04OFF02N02CB2SK3Epo2Eq4Ersv3RSV2NES2K03S162N03FIT2CB2SK3EpoS2K03S16S2K02CBS2K0S2K0S2K04OFF02CB3EpoS2K0S2K0S2K0S2K0S2K02CBS2K04OFF02CB3EpoS2K0S2K02CB2SK3Epo4Ersv3RSVS2K02CB3Epo4Ersv3RSVS2K02QBS2K0S2K03S313RSVS2K0S2K03S164OFF02N03FIT2CB2SK3EpoS2K03S162N02CB2SK3Epo4Ersv3RSVS2K03S16S2K02CBS2K02CB2SK3Epo4Ersv3RSV2R21HS2K0S2K0S2K03S16S2K03S16S2K04OFF02CB2SK3EpoS2K0S2K0S2K0S2K0S2K04OFF02CB3EpoS2K02CB3Epo4Ersv3RSVS2K03RSV2GTS2K0S2K0S2K0S2K0S2K0S2K0S2K0".
rewrite (wr16_wr8_comm (fst b, snd b + (UNIT + stride * k) + -2) (fst b, snd b + (UNIT + stride * k) + -3)) by (cbn; lia || reflexivity).
      destruct (rwr8_rep st2 m4 (snd b + (UNIT + stride * k) + -3) 224 MR TK eq_refl eq_refl) as [M1 T1]; [unfold UNIT; lia| lia|].
      destruct (rwr16_rep _ _ (snd b + (UNIT + stride * k) + -2) off M1 T1 eq_refl eq_refl) as [M2 T2]; [unfold UNIT; lia| unfold UNIT; lia| lia|].
      destruct (rwr8_rep _ _ (snd b + (UNIT + stride * k) + UNIT * off + -4) 0 M2 T2 eq_refl eq_refl) as [M3 T3]; [unfold UNIT; lia| lia|].
      unfold UNIT in *.
      replace (P0 - 2) with (r_base r + (snd b + (16 + stride * k) + -2)) by (unfold P0; lia).
      replace (P0 - 3) with (r_base r + (snd b + (16 + stride * k) + -3)) by (unfold P0; lia).
      replace (P0 + 16 * off - 4) with (r_base r + (snd b + (16 + stride * k) + 16 * off + -4)) by (unfold P0; lia).
      split; [exact M3|]. split; [exact T3|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros; reflexivity. }
  clearbody stC. destruct stC as [stc p']. cbn [fst snd] in PRE. destruct PRE as (MC & TC & -> & ERc & EGc & CONCc).
  cbn [fst snd].
  unfold renframe_tail_mem. cbv zeta.
  (* [comment removed for export] *)
  set (po := snd b + (UNIT + stride * k) + UNIT * off).
  assert (Epo : P0 + 16 * off = r_base r + po) by (unfold po, P0, UNIT; lia).
  assert (Eq : (P0 + 16 * off - B - 16) / 16 = (po - (snd b + UNIT)) / UNIT).
  { unfold po, P0, UNIT. f_equal; lia. }
  rewrite Eq.
  assert (QB : 0 <= (po - (snd b + UNIT)) / UNIT < 65536).
  { unfold po, UNIT. replace (snd b + (16 + stride * k) + 16 * off - (snd b + 16)) with (stride * k + 16 * off) by lia.
    split; [apply Z.div_pos; lia| exact Q16]. }
  (* [comment removed for export] *)
  rewrite (wr16_wr8_comm (fst b, po + -2) (fst b, po + -3)) by (cbn; lia || reflexivity).
  destruct (rwr8_rep _ _ (po + -3) k MC TC ERc EGc) as [MD TD]; [unfold po, UNIT; lia| lia|].
  destruct (rwr16_rep _ _ (po + -2) ((po - (snd b + UNIT)) / UNIT) MD TD ERc EGc) as [ME TE]; [unfold po, UNIT; lia| unfold po, UNIT; lia| lia|].
  replace (P0 + 16 * off - 2) with (r_base r + (po + -2)) by lia.
  replace (P0 + 16 * off - 3) with (r_base r + (po + -3)) by lia.
  (* [comment removed for export] *)
  unfold set_size, aadd. cbn [fst snd id].
  set (rsv := snd b + (UNIT + stride * k) + (stride - IB) - po - n).
  assert (Ersv : P0 + stride - 4 - (P0 + 16 * off) - n = rsv) by (unfold rsv, po, P0, UNIT, IB; lia).
  rewrite Ersv.
  assert (RSV : 0 <= rsv <= stride - 4 - n) by (unfold rsv, po, UNIT, IB; lia).
  set (stF := if negb (rsv =? 0) then _ else _).
  set (mF := if rsv =? 0 then _ else _).
  assert (PF : rmrep stF mF /\ ticks_ok stF /\ s_regions stF = s_regions st2 /\ s_groups stF = s_groups st2).
  { subst stF mF. destruct (Z.eqb_spec rsv 0) as [E|NE]; cbn [negb].
    - split; [exact ME|]. split; [exact TE|]. split; assumption.
    - destruct (rwr8_rep _ _ (snd b + (UNIT + stride * k) + (stride - IB) + - rsv) 0 ME TE ERc EGc) as [MF TF]; [unfold rsv, po, UNIT, IB; lia| lia|].
      replace (P0 + stride - 4 - rsv) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + - rsv)) by (unfold P0, UNIT, IB; lia).
      split; [exact MF|]. split; [exact TF|]. split; assumption. }
  clearbody stF mF. destruct PF as (MF & TF & ERf & EGf).
  set (stG := if 5 <=? rsv then _ else _).
  set (mG := if 5 <=? rsv then _ else _).
  assert (PG : rmrep (fst stG) (fst mG) /\ ticks_ok (fst stG) /\ snd stG = snd mG /\ 0 <= snd mG <= 5
                /\ s_regions (fst stG) = s_regions st2 /\ s_groups (fst stG) = s_groups st2).
  { subst stG mG. destruct (Z.leb_spec 5 rsv) as [LE|GT]; cbn [fst snd].
    - (* [comment removed for export] *)
      rewrite (wr32_wr8_comm (fst b, snd b + (UNIT + stride * k) + (stride - IB) + -4) (fst b, snd b + (UNIT + stride * k) + (stride - IB) + -5)) by (cbn; lia || reflexivity).
      destruct (rwr8_rep _ _ (snd b + (UNIT + stride * k) + (stride - IB) + -5) 0 MF TF ERf EGf) as [M1 T1]; [unfold UNIT, IB; lia| lia|].
      destruct (rwr32_rep _ _ (snd b + (UNIT + stride * k) + (stride - IB) + -4) rsv M1 T1 ERf EGf) as [M2 T2]; [unfold UNIT, IB; lia| unfold UNIT, IB; lia| lia|].
      replace (P0 + stride - 4 - 4) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + -4)) by (unfold P0, UNIT, IB; lia).
      replace (P0 + stride - 4 - 5) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + -5)) by (unfold P0, UNIT, IB; lia).
      split; [exact M2|]. split; [exact T2|]. split; [reflexivity|]. split; [lia|]. split; assumption.
    - split; [exact MF|]. split; [exact TF|]. split; [reflexivity|]. split; [lia|]. split; assumption. }
  clearbody stG mG. destruct stG as [stg r1]. destruct mG as [mg r2]. cbn [fst snd] in PG |- *.
  destruct PG as (MG & TG & -> & R2 & ERg & EGg).
  assert (KV : 0 <= Z.land k 31 + Z.shiftl r2 5 < 256).
  { rewrite Z.shiftl_mul_pow2 by lia. change (2^5) with 32.
    assert (0 <= Z.land k 31 <= k) by (split; [apply Z.land_nonneg; lia| apply land_le_l; lia]). lia. }
  destruct (rwr8_rep _ _ (po + -3) (Z.land k 31 + Z.shiftl r2 5) MG TG ERg EGg) as [MH TH]; [unfold po, UNIT; lia| exact KV|].
  split; [exact MH|]. split; [exact TH|].
  split; [|split; [reflexivity| unfold po, UNIT; lia]].
  rewrite (conc_region' st2 (fst b, po) r Hr). cbn [snd]. exact (eq_sym Epo).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End ENFRAME.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma rpres_enframe : forall (C : Z -> Prop) m0 m4 P0 stride off n k B,
  rpres_except C m0 m4 ->
  0 <= off -> 0 <= n -> 16 * off + n + 4 <= stride -> 4 <= P0 -> P0 + stride <= 2^64 ->
  (forall x, P0 - 4 <= x < P0 + stride - 4 -> C x) ->
  rpres_except C m0 (renframe_tail_mem (renframe_off_mem m4 P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16)).
Proof.
  intros C m0 m4 P0 stride off n k B HP OFF0 N0 FIT P4 PS HC.
  assert (L2 : forall w, length (le2 w) = 2%nat) by (intros; reflexivity).
  assert (L4 : forall w, length (le4 w) = 4%nat) by (intros; reflexivity).
  assert (HO : rpres_except C m0 (renframe_off_mem m4 P0 off)).
  { unfold renframe_off_mem. destruct (off =? 0); [exact HP|].
    Local Ltac2 Set LiaHints.tbl := fun () => "00I0>15001278315.2815003380563.2115003380563.2215003380563.2615003380563.3117317660645.1921472299690.2631033904341.1932805229776.1938911633110.2938912055157.2044076581204.2445508904211.2045509014704.2946133491348.2446539283258.2648819153349.204886104128.19 58630455040.1959338250307.2060242812106.266175532259.26 64024432250.2664026472518.196434264131.26 00000B00Q00`01201A01E01I01M01]01f01o02;02F02Q02Y02g03003@03I03T03b03i03m048049S4OFF02N03FIT2H01HS4OFF02N03FIT1HS4OFF02N03FIT1HS4OFF02N03FIT2n01HS4OFF02N03FIT1HS2P4S2PSS2P4S4OFF02N03FIT2PSS4OFF02P4S4OFF02P4S4OFF02N02P4S2N03FIT2PSS2N03FIT2PSS3FIT2PSS4OFF02N02P41HS4OFF02P4S4OFF02N03FIT2PSS4OFF02P4S2N03FIT2PSS4OFF02N02P41HS3FIT1HS2PSS2N03FIT2PSS".
apply rpres_write; [| lia | cbn; lia | cbn; intros; apply HC; lia].
    apply rpres_write; [| lia | rewrite L2; lia | rewrite L2; intros; apply HC; lia].
    apply rpres_write; [exact HP| lia | cbn; lia | cbn; intros; apply HC; lia]. }
  unfold renframe_tail_mem. cbv zeta.
  set (mE := write_to_mem (write_to_mem (renframe_off_mem m4 P0 off) _ _) _ _).
  assert (HE : rpres_except C m0 mE).
  { subst mE. apply rpres_write; [| lia | rewrite L2; lia | rewrite L2; intros; apply HC; lia].
    apply rpres_write; [exact HO| lia | cbn; lia | cbn; intros; apply HC; lia]. }
  clearbody mE.
  set (rsv := P0 + stride - 4 - (P0 + 16 * off) - n).
  set (mF := if rsv =? 0 then _ else _).
  assert (HF : rpres_except C m0 mF).
  { subst mF. destruct (Z.eqb_spec rsv 0); [exact HE|]. apply rpres_write; [exact HE| lia | cbn; lia | cbn; intros; apply HC; lia]. }
  clearbody mF.
  set (mG := if 5 <=? rsv then _ else _).
  assert (HG : rpres_except C m0 (fst mG) /\ 0 <= snd mG <= 5).
  { subst mG. destruct (Z.leb_spec 5 rsv); cbn [fst snd].
    - split; [|lia]. apply rpres_write; [| lia | rewrite L4; lia | rewrite L4; intros; apply HC; lia].
      apply rpres_write; [exact HF| lia | cbn; lia | cbn; intros; apply HC; lia].
    - split; [exact HF| lia]. }
  clearbody mG. destruct mG as [mg r2]. cbn [fst snd] in HG |- *. destruct HG as [HG R2].
  apply rpres_write; [exact HG| lia | cbn; lia | cbn; intros; apply HC; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma rrdv_agree : forall st (m1 o : mem) (q : aptr) r (x : byte),
  rmrep st m1 -> unk_agree st o m1 ->
  (s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
  ~ grp_hdr_cov st (fst q) (snd q) ->
  bytes_at usegs m1 (r_base r + snd q) [x] ->
  rdv pans_mem o st q = bv_unsigned x.
Proof.
  intros st m1 o q r x MR UA Hr Hk Ho NG Hb.
  unfold rdv. destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
  - destruct (rmrep_shadow_read st m1 (fst q) r (snd q) v MR Hr Hk Ho E) as [RD Hv].
    Local Ltac2 Set LiaHints.tbl := fun () => "0070>15045125444.182744243528.22 36942846886.1844956394699.2055688452560.1662717045481.238931505686.23 00000100500600:00;00A00SSS2HoSS2HvSS2Ho1DS2Ho3RB03RBC5ATOPR".
pose proof (bytes_at_read usegs m1 _ [x] 0 1 Hb ltac:(lia) ltac:(cbn; lia)) as RD'. cbn [firstn skipn Z.to_nat] in RD'.
    rewrite Z.add_0_r in RD'. rewrite RD in RD'. inversion RD'. rewrite b8_unsigned by lia. reflexivity.
  - unfold pans_mem. rewrite (conc_region' st q r Hr).
    destruct Hb as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn in HB. rewrite Z.add_0_r in HB.
    unfold mrd in HB |- *. rewrite <- (UA (fst q) r (snd q) h Hr Hk Ho E NG).
    destruct (m1 (wa (r_base r + snd q))) as [b|] eqn:EMX; [inversion HB; subst; reflexivity|].
    exfalso. pose proof MR as ((_ & WR & _) & _). destruct (WR _ _ Hr) as (RB0 & _ & _ & RBC & RF). atop_facts.
    pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)) as D.
    rewrite ref_seg_rom_none in HB; [discriminate|]. rewrite wa_unsigned by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma rmeta_chunk_facts : forall st m g,
  rmrep st m -> meta_slot st g ->
  let G := conc st g in
  rw_cells usegs m G (meta_cells st (get_meta_rec st g))
  /\ 0 < G /\ G + 40 <= ATOP
  /\ (G + 40 <= 0x10000 \/ 0x1c000 <= G) /\ (G + 40 <= 0x1c000 \/ 0x4f000 <= G)
  /\ (forall rid' r', (s_regions st) !! rid' = Some r' -> r_kind r' = RKGroup ->
        G + 40 <= r_base r' \/ r_base r' + round_up_pg (r_len r') <= G)
  /\ (exists rid0 r0, (s_regions st) !! rid0 = Some r0 /\ r_kind r0 <> RKGroup
        /\ lr_lo r0 <= G /\ G + 40 <= r_base r0 + round_up_pg (r_len r0)).
Proof.
  intros st m g MR MS G.
  split; [apply rmrep_meta_chunk; assumption|].
  pose proof MR as (WF & _). pose proof WF as (_ & WR & DISJ & _).
  destruct MS as (a & ara & kk & Ha & Hkk & Eg).
  destruct (rarea_conc st a ara WF Ha) as (rga & Hra & Ca & Sa0 & Sa1 & SaL & NK & RaB0 & RaAL & RaC).
  pose proof (rarea_lr_lo st a ara rga WF Ha Hra) as LRa.
  destruct (WR (fst a) rga Hra) as (_ & _ & _ & _ & RFa). Local Ltac2 Set LiaHints.tbl := fun () => "0060>26357462884.3143515896150.3846486647401.3146520240177.315595508425.29 6659242212.31 00000V00l01<01M01V01fS3Hkk3Sa03Sa13SaL4RaB04RaAL3DA13DA22HGS3Hkk3LRa2HG1H3Sa13LR'S3Hkk3Sa13RaC2HGS3Hkk3Sa04RaB02HGS3Sa03Sa1S3Hkk3Sa13LRa2HG".
pose proof (rreserved_disjoint2 _ _ RFa ltac:(pose proof (round_up_pg_ge (r_len rga)); lia)) as [DA1 DA2].
  assert (HG : G = r_base rga + snd a + (AREA_HDR + META_SIZE * kk)).
  { subst G. rewrite Eg, conc_aadd by (rewrite Hra; eauto). rewrite (conc_region' st a rga Hra). reflexivity. }
  unfold AREA_HDR, META_SIZE, NSLOTS in HG, Hkk. clearbody G.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split.
  - intros rid' r' Hr' Hk'. pose proof (lr_lo_group r' Hk') as LR'.
    assert (NE : rid' <> fst a) by (intros ->; rewrite Hra in Hr'; inversion Hr'; subst; congruence).
    destruct (DISJ rid' r' (fst a) rga Hr' Hra NE); lia.
  - exists (fst a), rga. split; [exact Hra|]. split; [exact NK|]. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma rregion_facts : forall st m rid r,
  rmrep st m -> (s_regions st) !! rid = Some r ->
  4096 <= r_base r /\ r_base r mod 4096 = 0 /\ r_base r + round_up_pg (r_len r) <= ATOP
  /\ (0 < round_up_pg (r_len r) -> r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x1c000 <= r_base r)
  /\ (0 < round_up_pg (r_len r) -> r_base r + round_up_pg (r_len r) <= 0x1c000 \/ 0x4f000 <= r_base r).
Proof.
  intros st m rid r (WF & _) Hr. pose proof WF as (_ & WR & _).
  destruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
  split; [|split; [exact RBAL| split; [exact RBC| split; intros Hn; destruct (rreserved_disjoint2 _ _ RFr Hn); assumption]]].
  clear RFr. Local Ltac2 Set LiaHints.tbl := fun () => "0010>48779643421.1200000:S3RB04RBAL".
OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Section SLOT.
Variables (st : mstate) (m1 o : mem) (g b : aptr) (r : region) (idx n : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let B := conc st b.
Let P0 := B + 16 + stride * idx.

Hypothesis MR : rmrep st m1.
Hypothesis UA : unk_agree st o m1.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hr : (s_regions st) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis IDX : 0 <= idx.
Hypothesis SPAN : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis B16 : snd b mod 16 = 0.
Hypothesis SMOD : stride mod 16 = 0.
Hypothesis NOGRP : forall b' gh, (s_groups st) !! b' = Some gh -> fst b' = fst b ->
  snd b' + 9 <= snd b + 16 + stride * idx - 4 \/ snd b + 16 + stride * idx + stride - 4 <= snd b'.
Hypothesis HDR0 : cell_read (get_shadow st (fst b)) (snd b + 16 + stride * idx - 4) = Known 0.

#[using="MR UA Hr Hk B0 IDX SPAN S16 B16 SMOD HDR0"] Lemma rslot_facts :
  exists x3 x2 x1 : byte,
    wr_at usegs m1 (P0 - 4) stride
    /\ bytes_at usegs m1 (P0 - 4) [b8 0; b8 (bv_unsigned x3); b8 (bv_unsigned x2); b8 (bv_unsigned x1)]
    /\ rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -3) = bv_unsigned x3
    /\ rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2) = bv_unsigned x2
    /\ rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2 + 1) = bv_unsigned x1
    /\ B = r_base r + snd b /\ 4096 <= r_base r
    /\ P0 + stride <= r_base r + round_up_pg (r_len r) /\ r_base r + round_up_pg (r_len r) <= ATOP
    /\ (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x1c000 <= r_base r).
Proof.
  pose proof (rregion_facts st m1 (fst b) r MR Hr) as (R4 & RAL & RC & RI1 & RI2). atop_facts.
  assert (CB : B = r_base r + snd b) by (apply conc_region'; exact Hr).
  Local Ltac2 Set LiaHints.tbl := fun () => "00\0>10633947089.491065730742.49 11802115489.4813072842158.4914789919395.391603629458.49 16233624900.4918586380311.3319552178008.4622878330790.3724893064173.1525888422806.502742543465.49 27550839556.4927893251492.3929245549895.4929786706907.4029920600182.4030226908626.4734002134913.493407134468.49 36635884945.494245580456.48 44445786337.494600666923.48 46493120819.495013670869.49 50239149504.495325102278.49 56456628197.4656456641618.4756456642517.4856897696694.3757235885631.4958623704396.4959314955108.2061619511679.4963215677055.4764162715952.496433336498.49 65841136949.5068022693192.388394274504.48 8534399788.33 00000400B00I00\00d01701;01C01Q01b01c02402G02K02O02`02d03O03V03Z03^03b04304704>04B04P04^04l05E05^06706J06N06U06g07:07H07O07b07i08<08J08RS2B0S2B03S162R42CBS2B02HiS2B04SPAN3S162R42SKS2B03S16S2B04SPAN3S162R42SKS2B0S2B03S16S2B03S162R42SKS2B03S162R42CB2SKSS2B03S162R42CB2HiS2B04SPAN3S162R42SKS2B0S2B0S2B03S162R42CB2HiS2B0S2B04SPAN3S163B164SMOD2R43RAL3RI13RI22CB2SKS2B02HiS2B0S2B0S2B0S2B03S162R42CB2HiS2B0S2B02HiS2B0S2B03S162R42CBS2B03S162R42CBS2B03S162R42CBS2B04SPAN3S162R42RC5ATOPRS2B04SPAN3S162R42RC5ATOPRS2B04SPAN3S162R42RC5ATOPRS2B04SPAN3S162R42CBS2B0S2B02HiS3B162Hd2Hc3AL'2HqS2B04SPAN3S162R42CBS2B03S162R42SKS2B02HiS2B04SPAN3S162R42SKS2B02HiS2B04SPAN3S162R42SKS2B03S162R42SKS2B03IDX".
assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN.
  pose proof MR as (_ & _ & _ & _ & _ & SH). destruct (SH (fst b) r Hr Hk) as [HWr HB].
  assert (WRs : wr_at usegs m1 (P0 - 4) stride) by (eapply wr_at_sub; [exact HWr| unfold P0; lia| unfold P0; lia]).
  destruct (HB (snd b + 16 + stride * idx - 4) 0 ltac:(lia) HDR0) as [Y4 _].
  assert (WR3 : wr_at usegs m1 (P0 - 3) 3) by (eapply wr_at_sub; [exact WRs|lia|lia]).
  destruct (rwr_at_bytes_exist m1 (P0 - 3) 3 WR3 ltac:(lia) ltac:(unfold P0; lia)) as (bs & Lbs & Ybs).
  destruct bs as [|x3 [|x2 [|x1 [|? ?]]]]; try discriminate. clear Lbs.
  exists x3, x2, x1.
  assert (NG : forall d, 1 <= d <= 3 -> ~ grp_hdr_cov st (fst b) (snd b + 16 + stride * idx - d)).
  { intros d Hd (b' & gh & Hb' & Hf & Hc).
    pose proof MR as (WF' & _). destruct WF' as (_ & _ & _ & _ & WG). destruct (WG b' gh Hb') as (r' & _ & _ & _ & _ & AL').
    clear - Hd Hc AL' B16 SMOD IDX S16.
    destruct (Z.mod_divide stride 16 ltac:(lia)) as [D _]. destruct (D SMOD) as [q Hq].
    assert (E : stride * idx = 16 * (q * idx)) by (rewrite Hq; ring).
    set (w := q * idx) in E. clearbody w. OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  pose proof Ybs as (_ & _ & YB).
  assert (Y3 : bytes_at usegs m1 (r_base r + (snd b + 16 + stride * idx - 3)) [x3]).
  { split; [lia|]. split; [change (Z.of_nat (length [x3])) with 1; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia].
    pose proof (YB 0%nat ltac:(cbn; lia)) as YB0. cbn [nth_error Z.of_nat] in YB0 |- *.
    replace (r_base r + (snd b + 16 + stride * idx - 3) + 0) with (P0 - 3 + 0) by (unfold P0; lia). exact YB0. }
  assert (Y2 : bytes_at usegs m1 (r_base r + (snd b + 16 + stride * idx - 2)) [x2]).
  { split; [lia|]. split; [change (Z.of_nat (length [x2])) with 1; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia].
    pose proof (YB 1%nat ltac:(cbn; lia)) as YB1. cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ] in YB1 |- *.
    replace (r_base r + (snd b + 16 + stride * idx - 2) + 0) with (P0 - 3 + 1) by (unfold P0; lia). exact YB1. }
  assert (Y1 : bytes_at usegs m1 (r_base r + (snd b + 16 + stride * idx - 1)) [x1]).
  { split; [lia|]. split; [change (Z.of_nat (length [x1])) with 1; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia].
    pose proof (YB 2%nat ltac:(cbn; lia)) as YB2. cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ] in YB2 |- *.
    replace (r_base r + (snd b + 16 + stride * idx - 1) + 0) with (P0 - 3 + 2) by (unfold P0; lia). exact YB2. }
  split; [exact WRs|].
  split.
  { rewrite !b8_of_byte. change [b8 0; x3; x2; x1] with ([b8 0] ++ ([x3] ++ ([x2] ++ [x1]))).
    apply bytes_at_app. split; [eapply (bytes_at_at _ _ _ _ _ Y4); unfold P0; lia|]. cbn [length Z.of_nat Pos.of_succ_nat].
    apply bytes_at_app. split; [eapply (bytes_at_at _ _ _ _ _ Y3); unfold P0; lia|]. cbn [length Z.of_nat Pos.of_succ_nat].
    apply bytes_at_app. split; [eapply (bytes_at_at _ _ _ _ _ Y2); unfold P0; lia|]. cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat].
    eapply (bytes_at_at _ _ _ _ _ Y1); unfold P0; lia. }
  split.
  { apply (rrdv_agree st m1 o (fst b, _) r x3 MR UA Hr Hk); cbn [fst snd]; [lia| |].
    - replace (snd b + (16 + stride * idx) + -3) with (snd b + 16 + stride * idx - 3) by lia. apply NG; lia.
    - eapply bytes_at_at; [exact Y3| lia]. }
  split.
  { apply (rrdv_agree st m1 o (fst b, _) r x2 MR UA Hr Hk); cbn [fst snd]; [lia| |].
    - replace (snd b + (16 + stride * idx) + -2) with (snd b + 16 + stride * idx - 2) by lia. apply NG; lia.
    - eapply bytes_at_at; [exact Y2| lia]. }
  split.
  { apply (rrdv_agree st m1 o (fst b, _) r x1 MR UA Hr Hk); cbn [fst snd]; [lia| |].
    - replace (snd b + (16 + stride * idx) + -2 + 1) with (snd b + 16 + stride * idx - 1) by lia. apply NG; lia.
    - eapply bytes_at_at; [exact Y1| lia]. }
  split; [exact CB|]. split; [exact R4|]. split; [unfold P0; lia|]. split; [exact RC| apply RI1; unfold P0 in *; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End SLOT.

(* [comment removed for export] *)
Definition rmalloc_fp (st st' : mstate) (lo sp : Z) (a : Z) : Prop :=
  ralloc_fp (fun k => k <> RKGroup) st' lo sp a \/ new_reg_addr st st' a \/ free_slot_addr st a \/ grp_hdr_addr st a
  \/ fresh_addr st a.

#[using="Type"] Lemma rmalloc_fp_mono st sta stb lo sp a :
  (forall rid r, (s_regions sta) !! rid = Some r ->
     exists r', (s_regions stb) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
  rmalloc_fp st sta lo sp a -> rmalloc_fp st stb lo sp a.
Proof.
  intros HR [H|[H|H]]; [| right; left | right; right; exact H].
  - destruct H as [H|[H|[H|(rid & r & Hr & Hk & Ha)]]]; [left; left; exact H| left; right; left; exact H| left; right; right; left; exact H|].
    destruct (HR rid r Hr) as (r' & Hr' & K' & B' & L').
    left. right. right. right. exists rid, r'. split; [exact Hr'|]. split; [congruence|].
    assert (LRE : lr_lo r' = lr_lo r) by (unfold lr_lo; rewrite K', B'; reflexivity).
    pose proof (round_up_pg_mono (r_len r) (r_len r') L'). Local Ltac2 Set LiaHints.tbl := fun () => "0010>60907383215.2000000=S2Ha2B'3LRE1H".
lia.
  - destruct H as (rid & r & Hr & Hn & Ha). destruct (HR rid r Hr) as (r' & Hr' & K' & B' & L').
    exists rid, r'. split; [exact Hr'|]. split; [exact Hn|].
    assert (LRE : lr_lo r' = lr_lo r) by (unfold lr_lo; rewrite K', B'; reflexivity).
    pose proof (round_up_pg_mono (r_len r) (r_len r') L'). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FASTFACTS.
Variables (st : mstate) (LB : list block) (sc n : Z) (g : aptr) (k : Z) (t : N).
Let st1 := set_tick t st.
Let mr := get_meta_rec st g.
Let st2 := upd_meta g (m_set_avail (m_avail mr - 2 ^ k)) st1.
Hypothesis MF : RMFACTS st LB.
Hypothesis ACT : active st sc = Some g.
Hypothesis AV : 0 < m_avail mr.
Hypothesis K0 : 0 <= k.
Hypothesis LBK : lowbit (m_avail mr) = 2 ^ k.
Hypothesis N0 : 0 <= n.
Hypothesis NFIT : n + 4 <= 16 * size_class sc.

#[using="Type"] Lemma rget_meta_rec_st2 : get_meta_rec st2 g = m_set_avail (m_avail mr - 2 ^ k) mr.
Proof. unfold st2. rewrite get_meta_rec_upd_same. reflexivity. Qed.

#[using="rc LB sc MF ACT AV K0 LBK N0 NFIT"] Lemma rfast_slot_ok : exists b r,
  slot_ok st2 g b r k n
  /\ (forall a, r_base r + snd b + 16 + get_stride mr * k - 4 <= a < r_base r + snd b + 16 + get_stride mr * k + get_stride mr - 4 ->
        free_slot_addr st a)
  /\ k < 32 /\ m_mem mr = Some b /\ (s_regions st) !! (fst b) = Some r.
Proof.
  pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
  destruct (FA sc g ACT) as (SC48 & GSC & MEMnn). change (get_meta_rec st g) with mr in GSC, MEMnn.
  destruct (m_mem mr) as [b|] eqn:Hmem; [|congruence]. clear MEMnn.
  pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
  specialize (FG g b Hmem). change (get_meta_rec st g) with mr in FG. cbv zeta in FG.
  destruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh & AI & AVAI) & (r & Hr & Hk & B0 & B16 & SPAN) & S16 & SMOD & S31 & UND & S20).
  unfold UNIT, IB in *.
  assert (TBk : Z.testbit (m_avail mr) k = true) by (apply lowbit_testbit; assumption).
  pose proof (AVAI k K0 TBk) as KAI.
  Local Ltac2 Set LiaHints.tbl := fun () => "00M0>11065263809.581227632238.55 15371125219.5816046084485.5521381334151.592493336169.55 28223197268.5728223197268.5928225291711.5631084497720.5232291209103.5537185405350.4739542225681.5541418039500.4843149772559.5547404385131.6049735958931.4951792458685.4851796692231.5752278251594.5552566885022.55540560938.56  61966796934.5562062374277.5064967714191.5565100845346.5565502415534.6066515803890.558201950506.55 00000H00Z00k01>01P01W01_01g01o02A02I02[02_02c02k03C03W03^03e04704B04T04\05105905G05K05`05iS2K02B04SPAN3S162Ha1H2H0S2K02AI2B03S163KAIS2K02N02B03S162OFS2K03AVr2B03S163P2kS2K02AI2B03S163KAIS2LI2B0S2B03S16S2B03S16S2B03S16S2K02AI2B03S163KAIS3MPL2B0S2LI2AI2B03S163KAIS2B0S2B0S3FRr2B0S2K02N02B03S163S202OF2H0S2K04SC483GSC2B03S16S2K02B0S2K02B0S2K04NFIT2B03S161US2LI3GS02B0S2K02AI2B03S163KAIS2B03B16S2K03E632B03S165GSC48S2B03S16S2K02FB2B03S16S2B0S2K02N02LI2B03S163S20S2B04SPAN".
assert (K32 : k < 32) by lia.
  assert (P2k : 0 < 2 ^ k <= m_avail mr).
  { split; [apply Z.pow_pos_nonneg; lia|]. destruct (lowbit_pow2 (m_avail mr) AV) as (k' & _ & E' & LE'). unfold lowbit in LBK.
    rewrite LBK in E'. rewrite E'. exact LE'. }
  assert (GSC48 : m_sizeclass mr < 48) by lia. specialize (S31 GSC48).
  destruct SCr as [[GS0 MPL]|[E63 _]]; [|lia].
  pose proof (mf_free_clear _ _ MF g b k Hmem K0 (or_introl TBk)) as FC. cbv zeta in FC. destruct FC as [NOGRP _].
  change (get_meta_rec (strip st) g) with mr in NOGRP. change (s_groups (strip st)) with (s_groups st) in NOGRP.
  unfold sstart_of in NOGRP. rewrite Hmem in NOGRP. cbn [default from_option id snd] in NOGRP. unfold UNIT, IB in NOGRP.
  pose proof (mf_hdr0 _ _ MF g b k Hmem ltac:(change (get_meta_rec st g) with mr; lia)) as K4.
  unfold sstart_of in K4. rewrite Hmem in K4. cbn [default from_option id fst snd] in K4.
  change (get_meta_rec st g) with mr in K4. unfold IB, UNIT in K4.
  unfold sstart_of in SPAN. rewrite Hmem in SPAN. cbn [default from_option id snd] in SPAN. unfold UNIT, IB in SPAN.
  exists b, r. pose proof rget_meta_rec_st2 as E2.
  split; [|split; [|split; [exact K32| split; [reflexivity| exact Hr]]]].
  - pose proof (UND GSC48 k K0 TBk) as U. rewrite GSC in U. specialize (S20 GSC48).
    constructor; rewrite ?E2; cbn [m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen m_set_avail];
      try change (get_stride (m_set_avail (m_avail mr - 2 ^ k) mr)) with (get_stride mr);
      first [ exact Hmem | exact Hr | exact Hk | exact MSL | exact K4 | exact NOGRP | exact N0 | exact SMOD
            | (pose proof (mf_slots_complete _ _ MF g b k Hmem ltac:(change (get_meta_rec (strip st) g) with mr; lia)) as SC;
               change (get_meta_rec (strip st) g) with mr in SC; unfold sstart_of in SC; rewrite Hmem in SC;
               cbn [default from_option id snd] in SC; unfold UNIT in SC; exact SC)
            | (intros off O0 OF;
               assert (get_stride mr * k + 16 * off < get_stride mr * (k + 1)) by lia;
               assert (get_stride mr * (k + 1) <= get_stride mr * (m_last_idx mr + 1)) by (apply Z.mul_le_mono_nonneg_l; lia);
               apply Z.div_lt_upper_bound; lia)
            | lia ].
  - intros a Ha. exists g, b, r, k. split; [exact Hmem|]. split; [exact Hr|]. split; [exact Hk|]. split; [exact K0|]. split; [left; exact TBk|].
    unfold sstart_of. rewrite Hmem. cbn [default from_option id snd]. unfold UNIT, IB. fold mr.
    assert (get_stride mr * k + get_stride mr <= get_stride mr * m_last_idx mr + get_stride mr) by (apply Z.add_le_mono_r; apply Z.mul_le_mono_nonneg_l; lia).
    assert (0 <= get_stride mr * k) by (apply Z.mul_nonneg_nonneg; lia).
    lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End FASTFACTS.

End CANSEC1.
