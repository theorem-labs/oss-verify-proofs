(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmStatics PmSpecs PmParSpecs PmTxtSpecs PmStep PmParKit PmFrame PgSrc.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PGSK.

Definition apartb (r : L5.range) (b : Z * Z) : bool := Z.leb (fst r + snd r) (fst b) || Z.leb (fst b + snd b) (fst r).
Definition keepb (lo hi : Z) (OB : list (Z * Z)) (r : L5.range) : bool :=
  (Z.leb (fst r + snd r) lo || Z.leb hi (fst r)) && forallb (apartb r) OB.

Lemma apartb_true r B m : apartb r (B, m) = true <-> (fst r + snd r <= B \/ B + m <= fst r).
Proof. unfold apartb. cbn [fst snd]. rewrite orb_true_iff, !Z.leb_le. tauto. Qed.

Lemma keepb_true lo hi OB r :
  keepb lo hi OB r = true <-> ((fst r + snd r <= lo \/ hi <= fst r) /\ (forall B m, In (B, m) OB -> fst r + snd r <= B \/ B + m <= fst r)).
Proof.
  unfold keepb. rewrite andb_true_iff, orb_true_iff, !Z.leb_le, forallb_forall. split.
  - intros [H1 H2]. split; [exact H1|]. intros B m Hin. apply (proj1 (apartb_true r B m)). apply H2. exact Hin.
  - intros [H1 H2]. split; [exact H1|]. intros [B m] Hin. apply (proj2 (apartb_true r B m)). apply H2. exact Hin.
Qed.

Lemma filter_incl {X : Type} (f : X -> bool) (l : list X) : incl (List.filter f l) l.
Proof. intros x Hx. apply filter_In in Hx. tauto. Qed.

Section Kit.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis KL : PMK.klayout segs L.
Hypothesis HIok : heap_iface_ok L SCFG HI.

Lemma in4 {X} (l1 l2 l3 l4 : list X) x : In x (l1 ++ l2 ++ l3 ++ l4) <-> In x l1 \/ In x l2 \/ In x l3 \/ In x l4.
Proof. rewrite !in_app_iff. tauto. Qed.

Lemma hpres_weaken LB LB2 sp scr W W2 M M' :
  L5C.hpres L LB2 sp scr W2 M M' -> incl LB LB2 -> (forall a, L5.outside W a -> L5.outside W2 a) -> L5C.hpres L LB sp scr W M M'.
Proof.
  intros HP INC HW. apply (PMK.hpres_of L LB sp scr W M M').
  - apply (PMK.ek_weaken L LB LB2 sp scr sp scr W W2 M M' (PMK.ek_of_hpres L LB2 sp scr W2 M M' HP) INC); [intros x Hx; exact Hx| exact HW].
  - exact (L5C.hpres_defined L LB2 sp scr W2 M M' HP).
  - exact (PMPK.dk_incl L LB LB2 sp scr M M' (PMK.dk_of_hpres L LB2 sp scr W2 M M' HP) INC).
Qed.

Theorem src_of_tw_ok (T : PGS.towner) (tb : PM.vstr) (tg : Z) :
  PGS.towner_ok segs A L HI T -> hl_ceil L <= PGS.tw_lo T -> 0x7fff80000000 <= hl_sptop L ->
  PGS.owner_ok segs A L HI (PGS.src_of_tw T tb tg).
Proof.
  intros [TS TL TU] CEIL SPT. pose proof (PMK.kl_img segs L KL) as KI. pose proof (PMK.kl_errno segs L KL) as KE.
  destruct TL as (L1 & L2 & L3 & L4 & L5' & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15).
  constructor; cbn [PGS.ow_at PGS.ow_os PGS.ow_ois PGS.ow_lo PGS.ow_hi PGS.ow_win PGS.src_of_tw].
  -   intros M src OB' (OB & -> & AT). destruct (TS M src tb tg OB AT) as (S1 & S2 & S3 & _ & _).
    split; [exact S1|]. split; [exact S2| exact S3].
  -   set (xos := PGS.tw_os T) in *. set (xois := PGS.tw_ois T) in *. set (xotb := PGS.tw_otb T) in *. set (xlo := PGS.tw_lo T) in *. set (xhi := PGS.tw_hi T) in *. repeat split; try lia.
  -
    intros LBX sp scr Wx M M' src src' OB' cr VM SP (OB & -> & AT) HH FA FB FC HP SF' QC.
    set (xos := PGS.tw_os T) in *. set (xois := PGS.tw_ois T) in *. set (xotb := PGS.tw_otb T) in *. set (xlo := PGS.tw_lo T) in *. set (xhi := PGS.tw_hi T) in *.
    exists OB. split; [reflexivity|].
    destruct (TS M src tb tg OB AT) as (SF & NI & DEF & VS & TBOK).
    set (BIG := PM.src_own src ++ (PM.vs_own tb ++ OB) ++ LBX) in *.
    assert (BIGE : BIG = (PM.src_own src ++ PM.vs_own tb) ++ (OB ++ LBX)) by (unfold BIG; rewrite <- !app_assoc; reflexivity).
    assert (BR : PMFR.brange L BIG) by (apply (PMFR.brange_of_heap L HI HIok BIG BIG cr M VM HH); apply incl_refl).
    assert (ND : NoDup (map fst BIG)) by exact (PMPK.heap_nodup L HI HIok BIG cr M VM HH).
    set (Wx0 := List.filter (keepb xlo xhi OB) Wx).

    assert (REJ : forall r, In r Wx -> keepb xlo xhi OB r = false ->
              ((exists n, tb = PM.VShort n) /\ xotb + 1 <= fst r /\ fst r + snd r <= xotb + 24)
              \/ (exists c n q, tb = PM.VLong c n q /\ q <= fst r /\ fst r + snd r <= q + c)).
    { intros r Hr KF. pose proof (proj1 (Forall_forall _ _) FC r Hr) as [[C1 C2]|[_ W]]; [|exact W].
      exfalso. assert (KT : keepb xlo xhi OB r = true); [|rewrite KT in KF; discriminate KF].
      apply (proj2 (keepb_true xlo xhi OB r)). split; [exact C1|]. intros B m Hin. apply (C2 B m). apply in_or_app. right. exact Hin. }

    assert (OWNF : forall B m, In (B, m) (PM.src_own src ++ PM.vs_own tb) ->
              B + m <= hl_ceil L /\ (B + m <= hl_img_lo L \/ hl_img_hi L <= B) /\
              (forall B' m', In (B', m') (OB ++ LBX) -> B + m <= B' \/ B' + m' <= B)).
    { intros B m Hin.
      assert (HB : In (B, m) BIG) by (rewrite BIGE; apply in_or_app; left; exact Hin).
      destruct (BR B m HB) as (Z0 & Z1 & Z4). split; [exact Z4|]. split; [exact Z1|].
      intros B' m' Hin'. assert (HB' : In (B', m') BIG) by (rewrite BIGE; apply in_or_app; right; exact Hin').
      apply (PMPK.blocks_apart_heap L HI HIok BIG cr M VM B m B' m' HH HB HB').
      apply (PMPK.fst_neq_app (PM.src_own src ++ PM.vs_own tb) (OB ++ LBX) B m B' m'); [rewrite <- BIGE; exact ND| exact Hin| exact Hin']. }

    assert (EK : PMK.ek L (OB ++ LBX) sp scr (PGS.W_srcfG xos xois ++ [(xotb, 24)] ++ Wx0) M M').
    { apply (PMPK.ek_drop_own L (PM.src_own src ++ PM.vs_own tb) (OB ++ LBX) sp scr _ (PGS.W_srcG xos xois src ++ Wx) M M').
      - rewrite <- BIGE. exact (PMK.ek_of_hpres L BIG sp scr _ M M' HP).
      - exact OWNF.
      - intros a OW.
        destruct (PMK.rng_dec a (PM.sr_qc src) (PM.sr_qc src + PM.CHUNK)) as [IC|NC].
        { right. exists (PM.sr_qc src), PM.CHUNK. split; [apply in_or_app; left; left; reflexivity| exact IC]. }
        assert (TBD : {exists c n q, tb = PM.VLong c n q /\ q <= a < q + c} + {forall c n q, tb = PM.VLong c n q -> ~ (q <= a < q + c)}).
        { destruct tb as [n|c n q]; [right; intros c n' q E; discriminate E|].
          destruct (PMK.rng_dec a q (q + c)) as [IQ|NQ]; [left; exists c, n, q; split; [reflexivity| exact IQ]|].
          right. intros c' n' q' E. injection E as <- <- <-. exact NQ. }
        destruct TBD as [(c & n & q & -> & IT)|NT].
        { right. exists q, c. split; [apply in_or_app; right; left; reflexivity| exact IT]. }
        left. intros r Hr Hin. apply in_app_or in Hr. destruct Hr as [Hr|Hr].
        + unfold PGS.W_srcG in Hr. apply in_app_or in Hr. destruct Hr as [Hr|[<-|[]]].
          * apply (OW r); [apply in_or_app; left; exact Hr| exact Hin].
          * unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exact (NC Hin).
        + destruct (keepb xlo xhi OB r) eqn:KB.
          * apply (OW r); [|exact Hin]. apply in_or_app. right. apply in_or_app. right. unfold Wx0. apply filter_In. split; [exact Hr| exact KB].
          * destruct (REJ r Hr KB) as [(_ & W1 & W2)|(c & n & q & E & W1 & W2)].
            -- apply (OW (xotb, 24)); [apply in_or_app; right; left; reflexivity|]. unfold L5.in_rng in *. cbn [fst snd]. lia.
            -- apply (NT c n q E). unfold L5.in_rng in Hin. lia. }
    apply (TU LBX sp scr Wx0 M M' src src' tb tb tg tg OB cr VM SP AT).
    +   unfold BIG in HH. rewrite <- app_assoc in HH. exact HH.
    +   apply Forall_forall. intros b Hb. apply (proj1 (Forall_forall _ _) FA b). rewrite app_assoc. exact Hb.
    +   intros b Hb. split.
      * apply FB. apply in_or_app. right. exact Hb.
      * intros B' m' Hin'. destruct b as [B m]. cbn [fst snd].
        destruct (OWNF B' m' ltac:(apply in_or_app; right; exact Hin')) as (_ & _ & AP).
        destruct (AP B m ltac:(apply in_or_app; left; exact Hb)); lia.
    +   apply Forall_forall. intros r Hr. unfold Wx0 in Hr. apply filter_In in Hr. destruct Hr as [_ KB].
      exact (proj1 (keepb_true xlo xhi OB r) KB).
    +
      apply (PMK.hpres_of L (OB ++ LBX) sp scr _ M M' EK).
      * exact (L5C.hpres_defined L BIG sp scr _ M M' HP).
      * apply (PMPK.dk_incl L (OB ++ LBX) BIG sp scr M M' (PMK.dk_of_hpres L BIG sp scr _ M M' HP)).
        intros b Hb. rewrite BIGE. apply in_or_app. right. exact Hb.
    + exact SF'.
    + exact QC.
    +
      assert (KEPT : forall a, xotb <= a < xotb + 24 -> (a = xotb \/ forall n, tb <> PM.VShort n) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha H0. apply (PMK.ek_of_hpres L BIG sp scr _ M M' HP a).
        split; [lia|]. split; [right; left; split; lia|]. split; [unfold in_errno; lia|].
        intros r Hr Hin. apply in_app_or in Hr. destruct Hr as [Hr|Hr].
        - unfold PGS.W_srcG, PGS.W_srcfG in Hr. apply in_app_or in Hr. unfold L5.in_rng in Hin.
          destruct Hr as [[<-|[<-|[<-|[]]]]|[<-|[]]]; cbn [fst snd] in Hin; try lia.
          assert (HB : In (PM.sr_qc src, PM.CHUNK) BIG) by (unfold BIG; apply in_or_app; left; left; reflexivity).
          destruct (BR _ _ HB) as (_ & _ & Z4). lia.
        - destruct (keepb xlo xhi OB r) eqn:KB.
          + apply (proj1 (keepb_true xlo xhi OB r)) in KB. destruct KB as [KB _]. unfold L5.in_rng in Hin. lia.
          + destruct (REJ r Hr KB) as [((n & E) & W1 & W2)|(c & n & q & E & W1 & W2)]; unfold L5.in_rng in Hin.
            * destruct H0 as [->|NS]; [lia| exact (NS n E)].
            * assert (HB : In (q, c) BIG) by (unfold BIG; rewrite E; apply in_or_app; right; apply in_or_app; left; left; reflexivity).
              destruct (BR _ _ HB) as (_ & _ & Z4). lia. }
      assert (DK : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> ((hl_ceil L <= a /\ sp <= a) \/ exists B m, In (B, m) BIG /\ B <= a /\ a + n <= B + m) ->
                   L5.defined M a n -> L5.defined M' a n).
      { intros a n Ha Hn CA D i Hi. apply (PMK.dk_of_hpres L BIG sp scr _ M M' HP (a + i)); [lia| | unfold in_errno; destruct CA as [[C C']|(B & m & Hin & HB & HE)]; [lia|]; destruct (BR _ _ Hin) as (_ & Z1 & _); lia| exact (D i Hi)].
        destruct CA as [[C C']|(B & m & Hin & HB & HE)]; [right; left; split; lia| left]. exists (B, m). split; [exact Hin| cbn; lia]. }
      destruct VS as (VD & VA & VR). split; [apply (DK xotb 24); [lia|lia|left; split; lia| exact VD]|]. split; [exact I|].
      destruct tb as [n|c n q].
      * destruct VR as (Hn & U8). split; [exact Hn|].
        apply (L5C.u8_at_agree segs M M' xotb); [intros i Hi; replace i with xotb by lia; apply KEPT; [lia| left; reflexivity]|lia|lia| exact U8].
      * destruct VR as (U0 & U1 & U2 & B1 & B2 & B3 & BD & BA).
        assert (AG : L5C.agree_on M M' xotb 24).
        { intros i Hi. apply KEPT; [lia| right; intros n' E; discriminate E]. }
        assert (HB : In (q, c) BIG) by (unfold BIG; apply in_or_app; right; apply in_or_app; left; left; reflexivity).
        destruct (BR _ _ HB) as (Z0 & Z1 & Z4).
        split; [apply (L5C.u64_at_agree segs M M' xotb); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia| exact U0]|].
        split; [apply (L5C.u64_at_agree segs M M' (xotb + 8)); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia| exact U1]|].
        split; [apply (L5C.u64_at_agree segs M M' (xotb + 16)); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia| exact U2]|].
        split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [|exact I].
        apply (DK q c); [lia|lia| right; exists q, c; split; [exact HB| lia]| exact BD].
    + exact TBOK.
  -
    intros M src OB' p k (OB & -> & AT) (Hk & WIN).
    set (xos := PGS.tw_os T) in *. set (xois := PGS.tw_ois T) in *. set (xotb := PGS.tw_otb T) in *. set (xlo := PGS.tw_lo T) in *. set (xhi := PGS.tw_hi T) in *.
    destruct (TS M src tb tg OB AT) as (_ & _ & _ & (VD & _ & VR) & _).
    split; [exact Hk|]. destruct WIN as [((n & ->) & W1 & W2)|(c & n & q & -> & W1 & W2)].
    + split; [intros i Hi; replace (p + i) with (xotb + (p - xotb + i)) by lia; apply VD; lia|].
      right. unfold PM.CHUNK. repeat split; lia.
    + destruct VR as (_ & _ & _ & _ & _ & _ & BD & _).
      split; [intros i Hi; replace (p + i) with (q + (p - q + i)) by lia; apply BD; lia|].
      left. exists q, c. split; [apply in_or_app; left; left; reflexivity| lia].
Qed.

End Kit.
End PGSK.
