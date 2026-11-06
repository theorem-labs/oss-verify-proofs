(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core
     PmLayout PmModel PmStatics PmSpecs PmParSpecs PmTxtSpecs PmStep PmParKit PmFrame PgSrc PgSrcKit PgV8.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PGVK.
Import PGSK.

Section Kit.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis KL : PMK.klayout segs L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Abbreviation v8_atP := (PGV8.v8_at segs PMSP.T3 PMSP.T4).

Theorem src_of_vw_ok (V : PGV8.vowner) (x : PGV8.v8) (g : Z) :
  PGV8.vowner_ok segs A L HI V -> hl_ceil L <= PGV8.vw_lo V -> 0x7fff80000000 <= hl_sptop L ->
  PGS.owner_ok segs A L HI (PGV8.src_of_vw V x g).
Proof.
  intros [TS TL TU] CEIL SPT. pose proof (PMK.kl_img segs L KL) as KI. pose proof (PMK.kl_errno segs L KL) as KE.
  destruct TL as (L1 & L2 & L3 & L4 & L5a & L5b & L5' & L5c & L6 & L7 & L7b & L8 & L9 & L10 & L11).
  constructor; cbn [PGS.ow_at PGS.ow_os PGS.ow_ois PGS.ow_lo PGS.ow_hi PGS.ow_win PGV8.src_of_vw].
  - (* [comment removed for export] *) intros M src OB' (OB & -> & AT). destruct (TS M src x g OB AT) as (S1 & S2 & S3 & _ & _).
    split; [exact S1|]. split; [exact S2| exact S3].
  - (* [comment removed for export] *) set (xos := PGV8.vw_os V) in *. set (xois := PGV8.vw_ois V) in *. set (xotb := PGV8.vw_ov V) in *. set (xlo := PGV8.vw_lo V) in *. set (xhi := PGV8.vw_hi V) in *. repeat split; try lia.
  - (* [comment removed for export] *)
    intros LBX sp scr Wx M M' src src' OB' cr VM SP (OB & -> & AT) HH FA FB FC HP SF' QC.
    set (xos := PGV8.vw_os V) in *. set (xois := PGV8.vw_ois V) in *. set (xotb := PGV8.vw_ov V) in *. set (xlo := PGV8.vw_lo V) in *. set (xhi := PGV8.vw_hi V) in *.
    exists OB. split; [reflexivity|].
    destruct (TS M src x g OB AT) as (SF & NI & DEF & VS & TBOK).
    set (BIG := PM.src_own src ++ (PGV8.v8_own x ++ OB) ++ LBX) in *.
    assert (BIGE : BIG = (PM.src_own src ++ PGV8.v8_own x) ++ (OB ++ LBX)) by (unfold BIG; rewrite <- !app_assoc; reflexivity).
    assert (BR : PMFR.brange L BIG) by (apply (PMFR.brange_of_heap L HI HIok BIG BIG cr M VM HH); apply incl_refl).
    assert (ND : NoDup (map fst BIG)) by exact (PMPK.heap_nodup L HI HIok BIG cr M VM HH).
    set (Wx0 := List.filter (keepb xlo xhi OB) Wx).
    (* [comment removed for export] *)
    assert (REJ : forall r, In r Wx -> keepb xlo xhi OB r = false ->
              exists b n c, x = PGV8.V8Blk b n c /\ b <= fst r /\ fst r + snd r <= b + c).
    { intros r Hr KF. pose proof (proj1 (Forall_forall _ _) FC r Hr) as [[C1 C2]|[_ W]]; [|exact W].
      exfalso. assert (KT : keepb xlo xhi OB r = true); [|rewrite KT in KF; discriminate KF].
      apply (proj2 (keepb_true xlo xhi OB r)). split; [exact C1|]. intros B m Hin. apply (C2 B m). apply in_or_app. right. exact Hin. }
    (* [comment removed for export] *)
    assert (OWNF : forall B m, In (B, m) (PM.src_own src ++ PGV8.v8_own x) ->
              B + m <= hl_ceil L /\ (B + m <= hl_img_lo L \/ hl_img_hi L <= B) /\
              (forall B' m', In (B', m') (OB ++ LBX) -> B + m <= B' \/ B' + m' <= B)).
    { intros B m Hin.
      assert (HB : In (B, m) BIG) by (rewrite BIGE; apply in_or_app; left; exact Hin).
      destruct (BR B m HB) as (Z0 & Z1 & Z4). split; [exact Z4|]. split; [exact Z1|].
      intros B' m' Hin'. assert (HB' : In (B', m') BIG) by (rewrite BIGE; apply in_or_app; right; exact Hin').
      apply (PMPK.blocks_apart_heap L HI HIok BIG cr M VM B m B' m' HH HB HB').
      apply (PMPK.fst_neq_app (PM.src_own src ++ PGV8.v8_own x) (OB ++ LBX) B m B' m'); [rewrite <- BIGE; exact ND| exact Hin| exact Hin']. }
    (* [comment removed for export] *)
    assert (EK : PMK.ek L (OB ++ LBX) sp scr (PGS.W_srcfG xos xois ++ [(xotb, 24)] ++ Wx0) M M').
    { apply (PMPK.ek_drop_own L (PM.src_own src ++ PGV8.v8_own x) (OB ++ LBX) sp scr _ (PGS.W_srcG xos xois src ++ Wx) M M').
      - rewrite <- BIGE. exact (PMK.ek_of_hpres L BIG sp scr _ M M' HP).
      - exact OWNF.
      - intros a OW.
        destruct (PMK.rng_dec a (PM.sr_qc src) (PM.sr_qc src + PM.CHUNK)) as [IC|NC].
        { right. exists (PM.sr_qc src), PM.CHUNK. split; [apply in_or_app; left; left; reflexivity| exact IC]. }
        assert (TBD : {exists b n c, x = PGV8.V8Blk b n c /\ b <= a < b + c} + {forall b n c, x = PGV8.V8Blk b n c -> ~ (b <= a < b + c)}).
        { destruct x as [|b n c]; [right; intros b n c E; discriminate E|].
          destruct (PMK.rng_dec a b (b + c)) as [IQ|NQ]; [left; exists b, n, c; split; [reflexivity| exact IQ]|].
          right. intros b' n' c' E. injection E as <- <- <-. exact NQ. }
        destruct TBD as [(b & n & c & -> & IT)|NT].
        { right. exists b, c. split; [apply in_or_app; right; left; reflexivity| exact IT]. }
        left. intros r Hr Hin. apply in_app_or in Hr. destruct Hr as [Hr|Hr].
        + unfold PGS.W_srcG in Hr. apply in_app_or in Hr. destruct Hr as [Hr|[<-|[]]].
          * apply (OW r); [apply in_or_app; left; exact Hr| exact Hin].
          * unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exact (NC Hin).
        + destruct (keepb xlo xhi OB r) eqn:KB.
          * apply (OW r); [|exact Hin]. apply in_or_app. right. apply in_or_app. right. unfold Wx0. apply filter_In. split; [exact Hr| exact KB].
          * destruct (REJ r Hr KB) as (b & n & c & E & W1 & W2). apply (NT b n c E). unfold L5.in_rng in Hin. lia. }
    apply (TU LBX sp scr Wx0 M M' src src' x x g g OB cr VM SP AT).
    + (* [comment removed for export] *) unfold BIG in HH. rewrite <- app_assoc in HH. exact HH.
    + (* [comment removed for export] *) apply Forall_forall. intros b Hb. apply (proj1 (Forall_forall _ _) FA b). rewrite app_assoc. exact Hb.
    + (* [comment removed for export] *) intros b Hb. split.
      * apply FB. apply in_or_app. right. exact Hb.
      * intros B' m' Hin'. destruct b as [B m]. cbn [fst snd].
        destruct (OWNF B' m' ltac:(apply in_or_app; right; exact Hin')) as (_ & _ & AP).
        destruct (AP B m ltac:(apply in_or_app; left; exact Hb)); lia.
    + (* [comment removed for export] *) apply Forall_forall. intros r Hr. unfold Wx0 in Hr. apply filter_In in Hr. destruct Hr as [_ KB].
      exact (proj1 (keepb_true xlo xhi OB r) KB).
    + (* [comment removed for export] *)
      apply (PMK.hpres_of L (OB ++ LBX) sp scr _ M M' EK).
      * exact (L5C.hpres_defined L BIG sp scr _ M M' HP).
      * apply (PMPK.dk_incl L (OB ++ LBX) BIG sp scr M M' (PMK.dk_of_hpres L BIG sp scr _ M M' HP)).
        intros b Hb. rewrite BIGE. apply in_or_app. right. exact Hb.
    + exact SF'.
    + exact QC.
    + (* [comment removed for export] *)
      assert (KEPT : forall a, xotb <= a < xotb + 24 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha. apply (PMK.ek_of_hpres L BIG sp scr _ M M' HP a).
        split; [lia|]. split; [right; left; split; lia|]. split; [unfold in_errno; lia|].
        intros r Hr Hin. apply in_app_or in Hr. destruct Hr as [Hr|Hr].
        - unfold PGS.W_srcG, PGS.W_srcfG in Hr. apply in_app_or in Hr. unfold L5.in_rng in Hin.
          destruct Hr as [[<-|[<-|[<-|[]]]]|[<-|[]]]; cbn [fst snd] in Hin; try lia.
          assert (HB : In (PM.sr_qc src, PM.CHUNK) BIG) by (unfold BIG; apply in_or_app; left; left; reflexivity).
          destruct (BR _ _ HB) as (_ & _ & Z4). lia.
        - destruct (keepb xlo xhi OB r) eqn:KB.
          + apply (proj1 (keepb_true xlo xhi OB r)) in KB. destruct KB as [KB _]. unfold L5.in_rng in Hin. lia.
          + destruct (REJ r Hr KB) as (b & n & c & E & W1 & W2); unfold L5.in_rng in Hin.
            assert (HB : In (b, c) BIG) by (unfold BIG; rewrite E; apply in_or_app; right; apply in_or_app; left; left; reflexivity).
            destruct (BR _ _ HB) as (_ & _ & Z4). lia. }
      assert (DK : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> ((hl_ceil L <= a /\ sp <= a) \/ exists B m, In (B, m) BIG /\ B <= a /\ a + n <= B + m) ->
                   L5.defined M a n -> L5.defined M' a n).
      { intros a n Ha Hn CA D i Hi. apply (PMK.dk_of_hpres L BIG sp scr _ M M' HP (a + i)); [lia| | unfold in_errno; destruct CA as [[C C']|(B & m & Hin & HB & HE)]; [lia|]; destruct (BR _ _ Hin) as (_ & Z1 & _); lia| exact (D i Hi)].
        destruct CA as [[C C']|(B & m & Hin & HB & HE)]; [right; left; split; lia| left]. exists (B, m). split; [exact Hin| cbn; lia]. }
      assert (AG : L5C.agree_on M M' xotb 24) by (intros i Hi; apply KEPT; lia).
      destruct x as [|b n c].
      * destruct VS as (VD & VA & U0 & U1 & U2). split; [apply (DK xotb 24); [lia|lia|left; split; lia| exact VD]|]. split; [exact I|].
        split; [apply (L5C.u64_at_agree segs M M' xotb); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia| exact U0]|].
        split; [apply (L5C.u64_at_agree segs M M' (xotb + 8)); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia| exact U1]|].
        apply (L5C.u64_at_agree segs M M' (xotb + 16)); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia| exact U2].
      * destruct VS as (VD & VA & U0 & U1 & U2 & B1 & B2 & B3 & B4 & BD & BA & BN).
        assert (HB : In (b, c) BIG) by (unfold BIG; apply in_or_app; right; apply in_or_app; left; left; reflexivity).
        destruct (BR _ _ HB) as (Z0 & Z1 & Z4).
        split; [apply (DK xotb 24); [lia|lia|left; split; lia| exact VD]|]. split; [exact I|].
        split; [apply (L5C.u64_at_agree segs M M' xotb); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia| exact U0]|].
        split; [apply (L5C.u64_at_agree segs M M' (xotb + 8)); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia| exact U1]|].
        split; [apply (L5C.u64_at_agree segs M M' (xotb + 16)); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia| exact U2]|].
        split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [| split; exact I].
        apply (DK b c); [lia|lia| right; exists b, c; split; [exact HB| lia]| exact BD].
    + exact TBOK.
  - (* [comment removed for export] *)
    intros M src OB' p k (OB & -> & AT) (Hk & (b & n & c & -> & W1 & W2)).
    destruct (TS M src _ g OB AT) as (_ & _ & _ & (VD & _ & _ & _ & _ & _ & _ & _ & _ & BD & _) & _).
    split; [exact Hk|].
    split; [intros i Hi; replace (p + i) with (b + (p - b + i)) by lia; apply BD; lia|].
    left. exists b, c. split; [apply in_or_app; left; left; reflexivity| lia].
Qed.

End Kit.
End PGVK.
