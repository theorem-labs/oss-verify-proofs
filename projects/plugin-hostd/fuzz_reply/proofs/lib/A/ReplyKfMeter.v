(* KF-COUNT (a Theorem Labs lane's row; a Theorem Labs lane's 09:2xZ decision): the allocator meter MT_sec that counts SECONDARY allocations.
   proves no function (kind: model lemma).
   Every allocating or freeing `_x` callee spec already has `mo_ok MT S (cost)` in its pre and `mo_le MT S S' (cost)` in
   its post, the cost being its request trace's tr_cost (lib/A/W_contract.v:944-951), and the arms and top_x take MT as
   a Variable.  At MT := MT_sec nsec KMAX:
     mo_malloc n = 1 for a secondary request (64,512 < n, = PresetRoom's not is_primary, sec_lit below), else 0;
     mo_free = 0;  mo_le s s' m = nsec s' <= nsec s + m;  mo_ok s m = nsec s + m <= KMAX.
   So each post states the count step of its trace and each pre asks that the count stays under KMAX.  nsec is a Theorem Labs lane's
   count of granted non-errbuf secondary entries of st_secs (nsec_cf, the cf layer); KMAX is reply's cf_kmax (2^23).
   This file is generic in both: MT_sec_laws (the meter laws ameter_laws asks), sec_lit, and MT_sec_set_fs (the meter
   does not see a frame-state change: W_rig_pro.v's MO_FR restated, a Theorem Labs lane / W8).  It Requires only Reusable and
   Spec, so image B's twin lib/B/ReplyKfMeterB.v is this text.  (ReplyCnt.Psec n is negb (PresetRoom.is_primary n).) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YM05 YG00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require PresetRoom.
Open Scope Z_scope.

Section m.
(* a Theorem Labs lane's count of granted non-errbuf secondary entries (nsec_cf) and the run bound (cf_kmax) *)
Variable nsec : astate -> Z.
Variable KMAX : Z.

Definition MT_sec : ameter_ops :=
  mkAMeter (fun s m => nsec s + m <= KMAX) (fun s s' m => nsec s' <= nsec s + m)
           (fun n => if 64512 <? n then 1 else 0) 0.

Lemma MT_sec_laws : ameter_laws MT_sec.
Proof.
  constructor; unfold MT_sec; cbn [mo_ok mo_le mo_malloc mo_free].
  - intros s. lia.
  - intros s1 s2 s3 m1 m2 H1 H2. lia.
  - intros s s' m m' H Hm. lia.
  - intros s m m' H Hm. lia.
  - intros s s' m1 m2 H1 H2. lia.
  - intros n _. destruct (64512 <? n); lia.
  - intros n n' Hn. destruct (Z.ltb_spec 64512 n); destruct (Z.ltb_spec 64512 n'); lia.
  - lia.
Qed.

(* the meter does not see a change of the frame state alone (set_fs keeps st_secs, so nsec_cf keeps it) *)
Lemma MT_sec_set_fs : (forall f s, nsec (set_fs f s) = nsec s) -> forall f s, mo_le MT_sec s (set_fs f s) 0.
Proof. intros H f s. cbn [mo_le MT_sec]. rewrite H. lia. Qed.
End m.

(* the literal 64,512 is PresetRoom's class rule: a request is secondary exactly when it is not primary *)
Lemma sec_lit : forall n, negb (PresetRoom.is_primary n) = (64512 <? n).
Proof.
  intros n.
  (* the redzone: at most 1024 bytes up to 64,512, exactly 2048 above *)
  assert (R : forall y, (y <= 64512 -> PresetRoom.rz_size y <= 1024) /\ (64512 < y -> PresetRoom.rz_size y = 2048)).
  { intros y. unfold PresetRoom.rz_size, PresetRoom.rz_log.
    assert (E : Z.shiftl 16 0 = 16 /\ Z.shiftl 16 1 = 32 /\ Z.shiftl 16 2 = 64 /\ Z.shiftl 16 3 = 128 /\
                Z.shiftl 16 4 = 256 /\ Z.shiftl 16 5 = 512 /\ Z.shiftl 16 6 = 1024 /\ Z.shiftl 16 7 = 2048)
      by (repeat split; reflexivity).
    destruct E as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7).
    destruct (Z.leb_spec y 48); [cbv iota; rewrite E0; lia|].
    destruct (Z.leb_spec y 96); [cbv iota; rewrite E1; lia|].
    destruct (Z.leb_spec y 448); [cbv iota; rewrite E2; lia|].
    destruct (Z.leb_spec y 3968); [cbv iota; rewrite E3; lia|].
    destruct (Z.leb_spec y 16128); [cbv iota; rewrite E4; lia|].
    destruct (Z.leb_spec y 32256); [cbv iota; rewrite E5; lia|].
    destruct (Z.leb_spec y 64512); cbv iota; [rewrite E6 | rewrite E7]; lia. }
  unfold PresetRoom.is_primary, PresetRoom.needed0, PresetRoom.rounded_size, PresetRoom.rup, PresetRoom.K_MAX_SIZE.
  destruct (R n) as (R1 & R2).
  set (x := Z.max n 8).
  assert (Hx : n <= x /\ 8 <= x /\ (n <= 8 \/ x = n)) by (unfold x; lia).
  pose proof (Z.div_mod (x + 8 - 1) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (x + 8 - 1) 8 ltac:(lia)) as M.
  set (q := (x + 8 - 1) / 8) in *.
  destruct (Z.ltb_spec 64512 n) as [L|L].
  - rewrite (R2 L). apply negb_true_iff. apply Z.leb_gt. lia.
  - specialize (R1 L). apply negb_false_iff. apply Z.leb_le. lia.
Qed.

Lemma MT_sec_malloc : forall nsec KMAX n,
  mo_malloc (MT_sec nsec KMAX) n = if negb (PresetRoom.is_primary n) then 1 else 0.
Proof. intros nsec KMAX n. rewrite sec_lit. reflexivity. Qed.
