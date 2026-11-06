(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState.
Import ListNotations.
Open Scope bv_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition wa (a : Z) : word := Z_to_bv 64 a.

Lemma wa_unsigned : forall a, (0 <= a < 2^64)%Z -> bv_unsigned (wa a) = a.
Proof. intros. unfold wa. apply unsigned_lit. assumption. Qed.

Lemma wa_succ : forall a, (wa a + 1 : word) = wa (a + 1).
Proof.
  intros. unfold wa. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  change (bv_unsigned (1 : word)) with 1%Z. unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma wa_eqb : forall a b, (0 <= a < 2^64)%Z -> (0 <= b < 2^64)%Z ->
  bv_eqb (wa a) (wa b) = Z.eqb a b.
Proof. intros. unfold bv_eqb. rewrite !wa_unsigned by assumption. reflexivity. Qed.

Lemma wa_add_nat : forall (a : word) i, a + Z_to_bv 64 (Z.of_nat i) = wa (bv_unsigned a + Z.of_nat i).
Proof.
  intros. unfold wa. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

Lemma firstn_skipn_step : forall {A} (bs : list A) k n b,
  nth_error bs k = Some b -> b :: firstn n (skipn (S k) bs) = firstn (S n) (skipn k bs).
Proof.
  intros A bs. induction bs as [|x bs IH]; intros k n b E.
  - destruct k; discriminate.
  - destruct k as [|k]; cbn in E.
    + inversion E; subst. reflexivity.
    + cbn [skipn]. apply IH. exact E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

Definition mrd (m : word -> option byte) (a : word) : option byte :=
  match m a with Some b => Some b | None => seg_rom segs a end.

#[using="Type"] Lemma rdn_unfold : forall m a n,
  rdn segs m a n = match n with
                   | O => Some []
                   | S n' => match mrd m a with
                             | Some b => match rdn segs m (a + 1) n' with Some r => Some (b :: r) | None => None end
                             | None => None end
                   end.
Proof. intros m a [|n']; reflexivity. Qed.

(* [comment removed for export] *)
Definition bytes_at (m : word -> option byte) (a : Z) (bs : list byte) : Prop :=
  (0 <= a)%Z /\ (a + Z.of_nat (length bs) <= 2^64)%Z /\
  forall i, (i < length bs)%nat -> mrd m (wa (a + Z.of_nat i)) = nth_error bs i.

(* [comment removed for export] *)
Definition wr_at (m : word -> option byte) (a : Z) (n : Z) : Prop :=
  (0 <= a)%Z /\ (a + n <= 2^64)%Z /\
  forall i, (0 <= i < n)%Z -> wview segs m (wa (a + i)) <> None.

(* [comment removed for export] *)
Definition ro_addr (a : word) : bool :=
  match find_segment segs (bv_unsigned a) 1 with
  | Some seg => negb (seg_writable seg)
  | None => false
  end.

(* [comment removed for export] *)
Definition mem_inv (m : word -> option byte) : Prop :=
  forall a b, m a = Some b -> ro_addr a = false.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma bytes_at_rdn : forall m a bs k n,
  bytes_at m a bs ->
  (k + n <= length bs)%nat ->
  rdn segs m (wa (a + Z.of_nat k)) n = Some (firstn n (skipn k bs)).
Proof.
  intros m a bs k n (Ha & Hlen & H). revert k.
  induction n as [|n IH]; intros k Hk.
  - reflexivity.
  - rewrite rdn_unfold. Local Ltac2 Set LiaHints.tbl := fun () => "0040>23057247784.1157606445901.1261212464951.1361432693865.1300000400:00>00BS2HkS2Hk1ES2HkS2Hk".
rewrite (H k) by lia.
    destruct (nth_error bs k) as [b|] eqn:E.
    2:{ apply nth_error_None in E. lia. }
    rewrite wa_succ. replace (a + Z.of_nat k + 1)%Z with (a + Z.of_nat (S k))%Z by lia.
    rewrite (IH (S k)) by lia.
    f_equal. apply firstn_skipn_step. exact E.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma bytes_at_ov_read : forall m a bs k n,
  bytes_at m a bs ->
  (k + n <= length bs)%nat ->
  ov_read_bytes segs m (wa (a + Z.of_nat k)) n = Some (firstn n (skipn k bs)).
Proof. intros. rewrite ov_rdn. apply bytes_at_rdn; assumption. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma bytes_at_read : forall m a bs (k : Z) n,
  bytes_at m a bs ->
  (0 <= k)%Z -> (Z.to_nat k + n <= length bs)%nat ->
  ov_read_bytes segs m (wa (a + k)) n = Some (firstn n (skipn (Z.to_nat k) bs)).
Proof.
  intros m a bs k n H Hk Hn. Local Ltac2 Set LiaHints.tbl := fun () => "0010=51794599521.9000007S2Hk2Hn".
rewrite <- (Z2Nat.id k) at 1 by lia.
  apply bytes_at_ov_read; assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma wr_at_store_ok : forall m a n (k : Z) (j : nat),
  wr_at m a n -> (0 <= k)%Z -> (k + Z.of_nat j <= n)%Z ->
  store_ok segs m (wa (a + k)) j = true.
Proof.
  intros m a n k j (Ha & Hn & H) Hk Hj. revert k Hk Hj.
  induction j as [|j IH]; intros k Hk Hj; [reflexivity|].
  cbn [store_ok]. destruct (wview segs m (wa (a + k))) eqn:E.
  2:{ exfalso. Local Ltac2 Set LiaHints.tbl := fun () => "0040>24320854122.1333695041164.143587275919.14 52988962809.1400000700;00B00FS2Hk2HjS2HjS2Hk2HjS2Hj".
apply (H k); [lia|exact E]. }
  rewrite wa_succ. replace (a + k + 1)%Z with (a + (k + 1))%Z by lia.
  apply (IH (k + 1)%Z); lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma write_to_mem_spec : forall bs m (a : Z) (x : word),
  (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
  write_to_mem m (wa a) bs x =
    if (Z.leb a (bv_unsigned x) && Z.ltb (bv_unsigned x) (a + Z.of_nat (length bs)))%bool
    then nth_error bs (Z.to_nat (bv_unsigned x - a))
    else m x.
Proof.
  induction bs as [|b bs IH]; intros m a x Ha Hl.
  - cbn [write_to_mem length].
    destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat 0)); cbn [andb]; try reflexivity.
    Local Ltac2 Set LiaHints.tbl := fun () => "00=0>28976388462.9 29156190763.1633749241086.9 56765667958.1059309037779.1659309037779.8 59309037904.1659309038033.1659309070547.1659309070672.1659309070801.1659315336847.1659315369869.1600000400@00G00Q00d00j01=01K01^02102B02R02bS2HlS2Hl2Hx1l2l2S2Ha2HlS2Ha2Hl2HxS2Hl2Hx1E1l2l02n01nS1l2l0S2Hl2Hx1E1l2l11n2l0S2Hl2Hx1E1l2l2S2Hl2Hx1E1l2n01n2l0S2Hl2Hx1E1l2n12n01nS2Hl2Hx1E2n12n21nS2Hl2Hx2n01l1E1nS2Hl2Hx1E1l2l01n".
exfalso; lia.
  - cbn [write_to_mem]. cbn [length] in Hl.
    rewrite wa_succ.
    rewrite (IH _ (a + 1)%Z x) by lia.
    pose proof (bv_unsigned_in_range 64 x) as Hx. unfold bv_modulus in Hx.
    assert (Ewa : bv_unsigned (wa a) = a) by (apply wa_unsigned; lia).
    unfold bv_eqb. rewrite Ewa. cbn [length].
    destruct (Z.eqb_spec (bv_unsigned x) a) as [E|E];
    destruct (Z.leb_spec0 (a+1) (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + 1 + Z.of_nat (length bs)));
    destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat (S (length bs)))); cbn [andb];
    try (exfalso; lia); try reflexivity.
    + rewrite E, Z.sub_diag. reflexivity.
    + replace (Z.to_nat (bv_unsigned x - a)) with (S (Z.to_nat (bv_unsigned x - (a + 1)))) by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma bytes_at_write_same : forall m a bs,
  (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
  bytes_at (write_to_mem m (wa a) bs) a bs.
Proof.
  intros m a bs Ha Hl. Local Ltac2 Set LiaHints.tbl := fun () => "00;0>1677449591.11 18484129204.8 18484129331.6 26983616514.8 26983617413.6 5448013527.10 59309037779.1059309070547.1059315336847.1059315369869.107985991279.8  00000900@00D00K00O00S00T00[00a00g011S2Hi2l01ES2Hl2HiS2HlS2Ha2HiS2HaS2HiFS2Hi2n0S2Hi1nS2Hi1nS2Ha2Hl2Hi".
split; [lia|]. split; [lia|].
  intros i Hi. unfold mrd. rewrite write_to_mem_spec by lia.
  rewrite wa_unsigned by lia.
  destruct (Z.leb_spec0 a (a + Z.of_nat i)); destruct (Z.ltb_spec0 (a + Z.of_nat i) (a + Z.of_nat (length bs))); cbn [andb]; try (exfalso; lia).
  replace (Z.to_nat (a + Z.of_nat i - a)) with i by lia.
  destruct (nth_error bs i) eqn:E; [reflexivity|]. apply nth_error_None in E. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma bytes_at_write_other : forall m a bs c cs,
  bytes_at m c cs ->
  (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
  (c + Z.of_nat (length cs) <= a \/ a + Z.of_nat (length bs) <= c)%Z ->
  bytes_at (write_to_mem m (wa a) bs) c cs.
Proof.
  intros m a bs c cs (Hc & Hcl & H) Ha Hal Hd. Local Ltac2 Set LiaHints.tbl := fun () => "0090>18484129204.1426983616514.1445407983785.1259309037779.1659309070547.1659315336847.1659315369869.1667759935995.1468390425587.1200000800?00D00P00Y00Z00[00f00jS3Hal2HiS2Ha2HiS3HclS2Hd2Hi1l2l0S2Hi1n2n0FFS2Hc3Hcl2HiS2Hc".
split; [lia|]. split; [lia|].
  intros i Hi. unfold mrd. rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
  destruct (Z.leb_spec0 a (c + Z.of_nat i)); destruct (Z.ltb_spec0 (c + Z.of_nat i) (a + Z.of_nat (length bs))); cbn [andb]; try (exfalso; lia);
  apply H; exact Hi.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Definition upd_bytes (cs : list byte) (k : nat) (bs : list byte) : list byte :=
  firstn k cs ++ bs ++ skipn (k + length bs) cs.

#[using="Type"] Lemma upd_bytes_length : forall cs k bs, (k + length bs <= length cs)%nat ->
  length (upd_bytes cs k bs) = length cs.
Proof.
  intros. unfold upd_bytes. rewrite !app_length, firstn_length, skipn_length. Local Ltac2 Set LiaHints.tbl := fun () => "0010=26143560480.5000003S1H".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma upd_bytes_nth : forall cs k bs i, (k + length bs <= length cs)%nat -> (i < length cs)%nat ->
  nth_error (upd_bytes cs k bs) i =
    if (Nat.leb k i && Nat.ltb i (k + length bs))%bool then nth_error bs (i - k) else nth_error cs i.
Proof.
  intros cs k bs i Hk Hi. unfold upd_bytes.
  destruct (Nat.leb_spec0 k i); destruct (Nat.ltb_spec0 i (k + length bs)); cbn [andb].
  - Local Ltac2 Set LiaHints.tbl := fun () => "00;0>2148436897.9  2154702079.9  3197498070.9  3203751050.9  34108321234.9 34114568844.9 40855510631.9 59309070547.1059309070672.1060821003904.9 65903982885.9 00000900E00P00\00h01101=01K01Z01e020S2Hk2Hi1lS2Hk2Hi1l2l0S2Hk2Hi1n1lS2Hk2Hi1n2n0S2Hk2Hi1l2l0S2Hk2Hi1lS2Hk2Hi1l2l0S2Hk2Hi1n1l2n0S2Hk2Hi1n2n02n1S2Hk2Hi1l1nS2Hk2Hi1l1n".
rewrite nth_error_app2 by (rewrite firstn_length; lia).
    rewrite firstn_length. replace (Nat.min k (length cs)) with k by lia.
    rewrite nth_error_app1 by lia. reflexivity.
  - rewrite nth_error_app2 by (rewrite firstn_length; lia).
    rewrite firstn_length. replace (Nat.min k (length cs)) with k by lia.
    rewrite nth_error_app2 by lia.
    rewrite nth_error_skipn. f_equal. lia.
  - rewrite nth_error_app1 by (rewrite firstn_length; lia).
    rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i k); [reflexivity| exfalso; lia].
  - rewrite nth_error_app1 by (rewrite firstn_length; lia).
    rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i k); [reflexivity| exfalso; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma nth_error_write : forall m a bs c cs i,
  bytes_at m c cs ->
  (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
  (i < length cs)%nat ->
  mrd (write_to_mem m (wa a) bs) (wa (c + Z.of_nat i)) =
    if (Z.leb a (c + Z.of_nat i) && Z.ltb (c + Z.of_nat i) (a + Z.of_nat (length bs)))%bool
    then nth_error bs (Z.to_nat (c + Z.of_nat i - a))
    else nth_error cs i.
Proof.
  intros m a bs c cs i (Hc & Hcl & H) Ha Hal Hi. unfold mrd. Local Ltac2 Set LiaHints.tbl := fun () => "0040>1671160770.16 18484129204.1326983616514.1367759935995.1300000<00D00K00VS2Hi1l2l02E2S3Hal2HiS2Ha2HiS2Hc3Hcl2Hi".
rewrite write_to_mem_spec by lia.
  rewrite wa_unsigned by lia.
  destruct (Z.leb_spec0 a (c + Z.of_nat i)); destruct (Z.ltb_spec0 (c + Z.of_nat i) (a + Z.of_nat (length bs))); cbn [andb];
  try (apply H; exact Hi).
  destruct (nth_error bs _) eqn:E2; [reflexivity|]. apply nth_error_None in E2. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma bytes_at_write_inside : forall m c cs (k : Z) bs,
  bytes_at m c cs ->
  (0 <= k)%Z -> (Z.to_nat k + length bs <= length cs)%nat ->
  bytes_at (write_to_mem m (wa (c + k)) bs) c (upd_bytes cs (Z.to_nat k) bs).
Proof.
  intros m c cs k bs Hat Hk Hkl. pose proof Hat as (Hc & Hcl & H).
  Local Ltac2 Set LiaHints.tbl := fun () => "00@0>30407616960.1843899514388.1444691106250.1445414272709.1259309037779.1859309037904.1859309038033.1859309070547.1859309070672.1859309070801.1859315336847.1859315369869.1864217341904.1264219434547.1467200705232.1468384130463.1200000A00O00[00d01901N01O01a02302A02S02c02h03003803@S2Hk3Hkl2Hi2l12l2S2Hk3Hkl2Hc2HiS3Hkl3Hcl2HiS3Hkl3HclS2Hk3Hkl2Hi1n2n02l01lS3Hkl2Hi1l1n2l12Hk2l0FS3Hkl2Hi1l2l01n2n0S3Hkl2Hi1l2n02n11nS3Hkl2Hi2n12n2S3Hkl2Hi1n2n02n11lS3Hkl2Hi2l02l11nS3HklS3Hkl2HiS3Hkl2HiS3Hkl2Hc".
split; [lia|]. split. { rewrite upd_bytes_length by lia. lia. }
  intros i Hi. rewrite upd_bytes_length in Hi by lia.
  rewrite (nth_error_write m (c + k) bs c cs i Hat) by lia.
  rewrite upd_bytes_nth by lia.
  destruct (Z.leb_spec0 (c + k) (c + Z.of_nat i)); destruct (Z.ltb_spec0 (c + Z.of_nat i) (c + k + Z.of_nat (length bs)));
  destruct (Nat.leb_spec0 (Z.to_nat k) i); destruct (Nat.ltb_spec0 i (Z.to_nat k + length bs)); cbn [andb]; try (exfalso; lia); try reflexivity.
  f_equal. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma wview_write_mono : forall m a bs x,
  wview segs m x <> None -> wview segs (write_to_mem m a bs) x <> None.
Proof.
  intros m a bs. revert m a. induction bs as [|b bs IH]; intros m a x H; cbn; [exact H|].
  apply IH. unfold wview in *. destruct (bv_eqb x a); [discriminate|]. exact H.
Qed.

#[using="Type"] Lemma wr_at_write : forall m a n c bs,
  wr_at m a n -> wr_at (write_to_mem m c bs) a n.
Proof.
  intros m a n c bs (Ha & Hn & H). Local Ltac2 Set LiaHints.tbl := fun () => "0030>26981515745.9 45601753963.9 62280508270.1100000400800<S2HaS2HnS2Hi".
split; [lia|]. split; [lia|].
  intros i Hi. apply wview_write_mono. apply H. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma write_to_mem_some : forall bs m (a : word) x b,
  write_to_mem m a bs x = Some b ->
  m x = Some b \/ (exists i, (i < length bs)%nat /\ x = wa (bv_unsigned a + Z.of_nat i)).
Proof.
  induction bs as [|b0 bs IH]; intros m a x b H; cbn in H.
  - left; exact H.
  - destruct (IH _ _ _ _ H) as [H1 | (i & Hi & Hx)].
    + destruct (bv_eqb x a) eqn:E.
      * right. exists 0%nat. Local Ltac2 Set LiaHints.tbl := fun () => "0050>10142874626.1230485888042.124112179971.11 45762403246.118929201186.12 00000400800900<00@S2HiS2HiSS1ES2H0".
split; [cbn; lia|]. unfold bv_eqb in E. apply Z.eqb_eq in E.
        apply bv_eq. rewrite wa_unsigned. 2:{ pose proof (bv_unsigned_in_range 64 a); unfold bv_modulus in *; cbn [Z.of_nat]; lia. }
        cbn [Z.of_nat]. lia.
      * left; exact H1.
    + right. exists (S i). split; [cbn; lia|]. rewrite Hx. unfold wa. apply bv_eq.
      rewrite !Z_to_bv_unsigned, bv_add_unsigned. change (bv_unsigned (1:word)) with 1%Z.
      unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma store_ok_wview : forall m a j i, store_ok segs m a j = true -> (i < j)%nat ->
  wview segs m (wa (bv_unsigned a + Z.of_nat i)) <> None.
Proof.
  intros m a j. revert a. Local Ltac2 Set LiaHints.tbl := fun () => "0030>10142872977.1010907088166.1019494984849.6 00000400800<S2HiS2HiS2Hi".
induction j as [|j IH]; intros a i Hs Hi; [lia|].
  cbn [store_ok] in Hs. destruct (wview segs m a) eqn:E; [|discriminate].
  destruct i as [|i].
  - replace (wa (bv_unsigned a + Z.of_nat 0)) with a. { rewrite E. discriminate. }
    unfold wa. apply bv_eq. rewrite Z_to_bv_unsigned. cbn [Z.of_nat]. rewrite Z.add_0_r, bv_wrap_small; [reflexivity|apply bv_unsigned_in_range].
  - specialize (IH (a + 1) i Hs ltac:(lia)).
    replace (wa (bv_unsigned a + Z.of_nat (S i))) with (wa (bv_unsigned (a + 1) + Z.of_nat i)); [exact IH|].
    unfold wa. apply bv_eq. rewrite !Z_to_bv_unsigned, bv_add_unsigned. change (bv_unsigned (1:word)) with 1%Z.
    unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma wview_not_ro : forall m a, wview segs m a <> None -> m a = None -> ro_addr a = false.
Proof.
  intros m a H Hm. unfold wview, ro_addr in *. rewrite Hm in H.
  destruct (find_segment segs (bv_unsigned a) 1) as [seg|]; [|reflexivity].
  destruct (seg_writable seg); [reflexivity|]. exfalso; apply H; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mem_inv_store : forall m a bs,
  mem_inv m -> store_ok segs m a (length bs) = true -> mem_inv (write_to_mem m a bs).
Proof.
  intros m a bs Hinv Hok x b Hx.
  destruct (write_to_mem_some _ _ _ _ _ Hx) as [H | (i & Hi & ->)].
  - exact (Hinv _ _ H).
  - pose proof (store_ok_wview _ _ _ _ Hok Hi) as W.
    destruct (m (wa (bv_unsigned a + Z.of_nat i))) eqn:E.
    + exact (Hinv _ _ E).
    + exact (wview_not_ro _ _ W E).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ro_byte (a : Z) (b : byte) : Prop :=
  seg_rom segs (wa a) = Some b /\ ro_addr (wa a) = true.

#[using="Type"] Lemma mem_inv_ro_read : forall m a b,
  mem_inv m -> ro_byte a b -> mrd m (wa a) = Some b.
Proof.
  intros m a b Hinv [Hro Hnw]. unfold mrd. destruct (m (wa a)) eqn:E.
  - exfalso. pose proof (Hinv _ _ E). congruence.
  - exact Hro.
Qed.

Fixpoint ro_bytes (a : Z) (bs : list byte) : Prop :=
  match bs with
  | [] => True
  | b :: bs' => ro_byte a b /\ ro_bytes (a + 1) bs'
  end.

#[using="Type"] Lemma ro_bytes_nth : forall bs a i b, ro_bytes a bs -> nth_error bs i = Some b -> ro_byte (a + Z.of_nat i) b.
Proof.
  induction bs as [|x bs IH]; intros a i b H Hn; [destruct i; discriminate|].
  destruct H as [H1 H2]. destruct i as [|i]; cbn in Hn.
  - inversion Hn; subst. rewrite Z.add_0_r. exact H1.
  - Local Ltac2 Set LiaHints.tbl := fun () => "0010>46731721467.10000001S".
replace (a + Z.of_nat (S i))%Z with (a + 1 + Z.of_nat i)%Z by lia. apply IH; assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma ro_bytes_at : forall m a bs,
  mem_inv m -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
  ro_bytes a bs -> bytes_at m a bs.
Proof.
  intros m a bs Hinv Ha Hl H. Local Ltac2 Set LiaHints.tbl := fun () => "0030>18486230103.8 26981515745.8 40252135361.1100000400800>S2HlS2HaS2Hi1E".
split; [lia|]. split; [lia|].
  intros i Hi. destruct (nth_error bs i) eqn:E. 2:{ apply nth_error_None in E; lia. }
  apply mem_inv_ro_read; [assumption|]. eapply ro_bytes_nth; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma bytes_at_app : forall m a bs1 bs2,
  bytes_at m a (bs1 ++ bs2) <-> bytes_at m a bs1 /\ bytes_at m (a + Z.of_nat (length bs1)) bs2.
Proof.
  intros m a bs1 bs2. unfold bytes_at. rewrite app_length. split.
  - intros (Ha & Hl & H). Local Ltac2 Set LiaHints.tbl := fun () => "00B0>13389178292.8 17133055562.1018484117869.1118486230103.8 19219970228.1023329203440.8 26981515745.8 26983627995.1136260350861.103897730774.14 44586719852.1447489100272.1062685393521.1064154507322.146618765165.11 6625061463.8  67144351114.1067150052877.1400000400;00@00D00K00R00Y00]00d00j01001701>01D01E01F01M01SS2HlS2Hl2HiS3Hl2S2HlS2Hl2HiS2Ha2HlS2Ha2HlS2HaS2Hl2HiS2Hi1nS2Hi1nS2Hl2HiS2Hl2HiS2Hi1nFFS2Hl2HiS2Hi1l".
repeat split; try lia.
    + intros i Hi. rewrite (H i) by lia. rewrite nth_error_app1 by lia. reflexivity.
    + intros i Hi. replace (a + Z.of_nat (length bs1) + Z.of_nat i)%Z with (a + Z.of_nat (length bs1 + i))%Z by lia.
      rewrite (H (length bs1 + i)%nat) by lia. rewrite nth_error_app2 by lia. f_equal. lia.
  - intros ((Ha & Hl1 & H1) & (Ha2 & Hl2 & H2)). repeat split; try lia.
    intros i Hi. destruct (Nat.ltb_spec0 i (length bs1)).
    + rewrite nth_error_app1 by lia. apply H1. lia.
    + rewrite nth_error_app2 by lia. rewrite <- (H2 (i - length bs1)%nat) by lia. f_equal. f_equal. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma bytes_at_nil : forall m a, (0 <= a <= 2^64)%Z -> bytes_at m a [].
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "0030=26981515745.436023694367.660770502117.400000300700:S1HS2HiS1H".
split; [lia|]. split; [cbn; lia|]. intros i Hi; cbn in Hi; lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma bytes_at_bound : forall m a bs, bytes_at m a bs -> (0 <= a /\ a + Z.of_nat (length bs) <= 2^64)%Z.
Proof. intros m a bs (Ha & Hl & _). Local Ltac2 Set LiaHints.tbl := fun () => "0010=34784170767.6000007S2Ha2Hl".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma bytes_at_ext : forall m a bs bs', bytes_at m a bs -> bs = bs' -> bytes_at m a bs'.
Proof. intros; subst; assumption. Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition le8 (v : word) : list byte := word_to_le_bytes 8 v.
Definition le4 (v : word) : list byte := Z_to_le_bytes 4 (bv_unsigned v).
Definition le2 (v : word) : list byte := Z_to_le_bytes 2 (bv_unsigned v).
Definition le1 (v : word) : list byte := Z_to_le_bytes 1 (bv_unsigned v).

Lemma length_Z_to_le_bytes : forall n z, length (Z_to_le_bytes n z) = n.
Proof. induction n; intros; cbn; [reflexivity| now rewrite IHn]. Qed.
Lemma length_le8 : forall v, length (le8 v) = 8%nat. Proof. intros; apply length_Z_to_le_bytes. Qed.
Lemma length_le4 : forall v, length (le4 v) = 4%nat. Proof. intros; apply length_Z_to_le_bytes. Qed.
Lemma length_le2 : forall v, length (le2 v) = 2%nat. Proof. intros; apply length_Z_to_le_bytes. Qed.
Lemma length_le1 : forall v, length (le1 v) = 1%nat. Proof. intros; apply length_Z_to_le_bytes. Qed.

Lemma bytes_le_to_Z_to_le_bytes : forall n z, (0 <= z)%Z ->
  bytes_le_to_Z (Z_to_le_bytes n z) = (z mod 2 ^ (8 * Z.of_nat n))%Z.
Proof.
  induction n as [|n IH]; intros z Hz.
  - cbn. rewrite Z.mod_1_r. reflexivity.
  - cbn [Z_to_le_bytes bytes_le_to_Z]. Local Ltac2 Set LiaHints.tbl := fun () => "00A0>15834755470.1219519706952.1120634880211.1124435884120.6 24996374994.1129856961236.1137042270522.7 37042273070.1046760913068.1250043647643.1251794599906.1053766219412.1155484508920.1155484508920.1257467540542.4 60744216926.1063368325619.1000000;00?00E00F00G00J00K00P00Y00d00h00l01901?01C01K01LS2Hw3Hw'2n1S2n0S2Hk1lSSS1lSS3Hw'S2Hw2n01lS2Hw3Hw'2n1S2HkS2n0S2Hw3Hw'2Hk1lS2Hk1lS2HzS2Hw3Hw'S".
rewrite IH by (apply Z.shiftr_nonneg; lia).
    rewrite Z_to_bv_unsigned. change (bv_wrap 8 z) with (z mod 2^8)%Z.
    set (w := (8 * Z.of_nat (S n))%Z). set (w' := (8 * Z.of_nat n)%Z).
    assert (Hw : (w = w' + 8)%Z) by lia. assert (Hw' : (0 <= w')%Z) by lia.
    apply Z.bits_inj'. intros k Hk.
    rewrite Z.lor_spec, Z.shiftl_spec by lia.
    rewrite <- !Z.land_ones by lia. rewrite !Z.land_spec.
    destruct (Z.ltb_spec0 k 8).
    + rewrite (Z.testbit_neg_r _ (k - 8)) by lia. rewrite (Z.ones_spec_low 8) by lia.
      rewrite (Z.ones_spec_low w) by lia. rewrite orb_false_r. reflexivity.
    + rewrite (Z.ones_spec_high 8) by lia. rewrite andb_false_r. rewrite orb_false_l.
      rewrite Z.shiftr_spec by lia. replace (k - 8 + 8)%Z with k by lia.
      destruct (Z.ltb_spec0 k w).
      * rewrite !Z.ones_spec_low by lia. reflexivity.
      * rewrite !Z.ones_spec_high by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma le_bytes_to_word_le8 : forall v : word, le_bytes_to_word (le8 v) = v.
Proof.
  intros v. unfold le_bytes_to_word, le8, word_to_le_bytes.
  rewrite bytes_le_to_Z_to_le_bytes by (apply bv_unsigned_in_range).
  apply bv_eq. rewrite Z_to_bv_unsigned. change (8 * Z.of_nat 8)%Z with 64%Z.
  pose proof (bv_unsigned_in_range 64 v) as Hr. unfold bv_modulus in Hr.
  Local Ltac2 Set LiaHints.tbl := fun () => "0010<3532037122.2000004S2Hr".
rewrite Z.mod_small by lia. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma bytes_le_to_Z_le4 : forall v : word, bytes_le_to_Z (le4 v) = (bv_unsigned v mod 2^32)%Z.
Proof. intros. unfold le4. rewrite bytes_le_to_Z_to_le_bytes by apply bv_unsigned_in_range. reflexivity. Qed.
Lemma bytes_le_to_Z_le2 : forall v : word, bytes_le_to_Z (le2 v) = (bv_unsigned v mod 2^16)%Z.
Proof. intros. unfold le2. rewrite bytes_le_to_Z_to_le_bytes by apply bv_unsigned_in_range. reflexivity. Qed.
Lemma bytes_le_to_Z_le1 : forall v : word, bytes_le_to_Z (le1 v) = (bv_unsigned v mod 2^8)%Z.
Proof. intros. unfold le1. rewrite bytes_le_to_Z_to_le_bytes by apply bv_unsigned_in_range. reflexivity. Qed.

Lemma Z_to_bv8_mod : forall x y, (x mod 2^8 = y mod 2^8)%Z -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof. intros. apply bv_eq. rewrite !Z_to_bv_unsigned. change (bv_wrap 8 ?a) with (a mod 2^8)%Z. exact H. Qed.

Lemma shiftr_mod_mod8 : forall z k w, (0 <= k)%Z -> (k + 8 <= w)%Z ->
  (Z.shiftr (z mod 2^w) k mod 2^8 = Z.shiftr z k mod 2^8)%Z.
Proof.
  intros z k w Hk Hw. apply Z.bits_inj'. intros i Hi.
  Local Ltac2 Set LiaHints.tbl := fun () => "0060=10351595562.724416777611.829011858828.852750324920.860744217176.763368325877.700000400:00=00I00P00QS2HiS2Hi1lS1nS2Hk2Hw2Hi1lS2Hk2HwS".
rewrite <- !Z.land_ones by lia. rewrite !Z.land_spec, !Z.shiftr_spec by lia.
  rewrite Z.land_spec.
  destruct (Z.ltb_spec0 i 8).
  - rewrite !Z.ones_spec_low by lia. rewrite !andb_true_r. reflexivity.
  - rewrite (Z.ones_spec_high 8) by lia. rewrite !andb_false_r. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma mod_mod8_of_modw : forall z w, (8 <= w)%Z -> ((z mod 2^w) mod 2^8 = z mod 2^8)%Z.
Proof.
  intros z w Hw. pose proof (shiftr_mod_mod8 z 0 w ltac:(lia) ltac:(lia)) as H.
  rewrite !Z.shiftr_0_r in H. exact H.
Qed.

Lemma Z_to_le_bytes_mod : forall n z w, (8 * Z.of_nat n <= w)%Z ->
  Z_to_le_bytes n (z mod 2^w) = Z_to_le_bytes n z.
Proof.
  induction n as [|n IH]; intros z w Hw; [reflexivity|].
  cbn [Z_to_le_bytes]. f_equal.
  - apply Z_to_bv8_mod. apply mod_mod8_of_modw. Local Ltac2 Set LiaHints.tbl := fun () => "0080=12152410230.512366024608.538879851526.546965617942.563189775093.563368324071.564274265972.59319827023.5 00000400800<00@00D00H00L00PS2HwS2HwS2HwS2HwS2HwS2HwS2HwS2Hw".
lia.
  - rewrite !Z.shiftr_div_pow2 by lia.
    replace w with (8 + (w - 8))%Z at 1 by lia. rewrite Z.pow_add_r by lia.
    rewrite Z.rem_mul_r by lia.
    rewrite <- (IH (z / 2^8)%Z (w - 8)%Z) by lia. f_equal.
    rewrite Z.mul_comm, Z.div_add by lia. rewrite (Z.div_small (z mod 2^8)) by (apply Z.mod_pos_bound; lia).
    rewrite Z.add_0_l. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Lemma store_bytes_8 : forall v : word, Z_to_le_bytes (width_bytes 64) (bv_unsigned v) = le8 v.
Proof. reflexivity. Qed.

Lemma store_bytes_4 : forall v : word, Z_to_le_bytes (width_bytes 32) (bv_unsigned (low32 v)) = le4 v.
Proof.
  intros. unfold le4, low32. cbn [width_bytes]. rewrite bv_extract_unsigned, Z.shiftr_0_r.
  change (bv_wrap 32 ?x) with (x mod 2^32)%Z. apply Z_to_le_bytes_mod. Local Ltac2 Set LiaHints.tbl := fun () => "0010=43581607276.1000001S".
cbn; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma store_bytes_2 : forall v : word, Z_to_le_bytes (width_bytes 16) (bv_unsigned (bv_extract 0 16 v)) = le2 v.
Proof.
  intros. unfold le2. cbn [width_bytes]. rewrite bv_extract_unsigned, Z.shiftr_0_r.
  change (bv_wrap 16 ?x) with (x mod 2^16)%Z. apply Z_to_le_bytes_mod. Local Ltac2 Set LiaHints.tbl := fun () => "0010=65062634604.1000001S".
cbn; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma store_bytes_1 : forall v : word, Z_to_le_bytes (width_bytes 8) (bv_unsigned (bv_extract 0 8 v)) = le1 v.
Proof.
  intros. unfold le1. cbn [width_bytes]. rewrite bv_extract_unsigned, Z.shiftr_0_r.
  change (bv_wrap 8 ?x) with (x mod 2^8)%Z. apply Z_to_le_bytes_mod. Local Ltac2 Set LiaHints.tbl := fun () => "0010=41452191724.1000001S".
cbn; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Definition zx32 (v : word) : word := Z_to_bv 64 (bv_unsigned v mod 2^32).
Definition sx32 (v : word) : word := Z_to_bv 64 (bv_swrap 32 (bv_unsigned v)).
Definition zx16 (v : word) : word := Z_to_bv 64 (bv_unsigned v mod 2^16).
Definition sx16 (v : word) : word := Z_to_bv 64 (bv_swrap 16 (bv_unsigned v)).
Definition zx8 (v : word) : word := Z_to_bv 64 (bv_unsigned v mod 2^8).
Definition sx8 (v : word) : word := Z_to_bv 64 (bv_swrap 8 (bv_unsigned v)).
Definition zxb (b : byte) : word := Z_to_bv 64 (bv_unsigned b).
Definition sxb (b : byte) : word := Z_to_bv 64 (bv_signed b).

Lemma zext_small : forall n (b : bv n) , zext 64 b = Z_to_bv 64 (bv_unsigned b).
Proof. intros. reflexivity. Qed.
Lemma sext_small : forall n (b : bv n), sext 64 b = Z_to_bv 64 (bv_signed b).
Proof. intros. reflexivity. Qed.

Lemma extract_low_mod : forall n (w : word), (0 < n)%N -> bv_unsigned (bv_extract 0 n w) = (bv_unsigned w mod 2^(Z.of_N n))%Z.
Proof. intros. rewrite bv_extract_unsigned, Z.shiftr_0_r. reflexivity. Qed.

Lemma signed_of_extract : forall n (w : word), (0 < n)%N ->
  bv_signed (bv_extract 0 n w) = bv_swrap n (bv_unsigned w).
Proof.
  intros. unfold bv_signed. rewrite extract_low_mod by assumption. unfold bv_swrap.
  f_equal. unfold bv_wrap, bv_modulus. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma le_bytes_to_word_le4 : forall v : word, bv_unsigned (le_bytes_to_word (le4 v)) = (bv_unsigned v mod 2^32)%Z.
Proof.
  intros. unfold le_bytes_to_word. rewrite Z_to_bv_unsigned, bytes_le_to_Z_le4.
  apply bv_wrap_small. unfold bv_modulus. pose proof (Z.mod_pos_bound (bv_unsigned v) (2^32)). Local Ltac2 Set LiaHints.tbl := fun () => "0010=40668734194.2000001S".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma le_bytes_to_word_le2 : forall v : word, bv_unsigned (le_bytes_to_word (le2 v)) = (bv_unsigned v mod 2^16)%Z.
Proof.
  intros. unfold le_bytes_to_word. rewrite Z_to_bv_unsigned, bytes_le_to_Z_le2.
  apply bv_wrap_small. unfold bv_modulus. pose proof (Z.mod_pos_bound (bv_unsigned v) (2^16)). Local Ltac2 Set LiaHints.tbl := fun () => "0010=40668734194.2000001S".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma le_bytes_to_word_le1 : forall v : word, bv_unsigned (le_bytes_to_word (le1 v)) = (bv_unsigned v mod 2^8)%Z.
Proof.
  intros. unfold le_bytes_to_word. rewrite Z_to_bv_unsigned, bytes_le_to_Z_le1.
  apply bv_wrap_small. unfold bv_modulus. pose proof (Z.mod_pos_bound (bv_unsigned v) (2^8)). Local Ltac2 Set LiaHints.tbl := fun () => "0010=40668734194.2000001S".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma le_bytes_to_word_byte : forall b : byte, bv_unsigned (le_bytes_to_word [b]) = bv_unsigned b.
Proof.
  intros. unfold le_bytes_to_word. cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r, Z_to_bv_unsigned.
  apply bv_wrap_small. pose proof (bv_unsigned_in_range 8 b). unfold bv_modulus in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010=30354061808.2000003S1H".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma load_u64 : forall v : word, bv_extract 0 64 (le_bytes_to_word (le8 v)) = v.
Proof.
  intros. rewrite le_bytes_to_word_le8. apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma zext_extract_le4 : forall v : word, zext 64 (bv_extract 0 32 (le_bytes_to_word (le4 v))) = zx32 v.
Proof.
  intros. rewrite zext_small. unfold zx32. f_equal. Local Ltac2 Set LiaHints.tbl := fun () => "0020=30228712271.138718438409.1000001002SS".
rewrite extract_low_mod by lia. rewrite le_bytes_to_word_le4.
  change (Z.of_N 32) with 32%Z. apply Z.mod_mod. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma zext_extract_le2 : forall v : word, zext 64 (bv_extract 0 16 (le_bytes_to_word (le2 v))) = zx16 v.
Proof.
  intros. rewrite zext_small. unfold zx16. f_equal. Local Ltac2 Set LiaHints.tbl := fun () => "0020=25163502857.130228712271.1000001002SS".
rewrite extract_low_mod by lia. rewrite le_bytes_to_word_le2.
  change (Z.of_N 16) with 16%Z. apply Z.mod_mod. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma zext_extract_le1 : forall v : word, zext 64 (bv_extract 0 8 (le_bytes_to_word (le1 v))) = zx8 v.
Proof.
  intros. rewrite zext_small. unfold zx8. f_equal. Local Ltac2 Set LiaHints.tbl := fun () => "0020=30228712271.138873133961.1000001002SS".
rewrite extract_low_mod by lia. rewrite le_bytes_to_word_le1.
  change (Z.of_N 8) with 8%Z. apply Z.mod_mod. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma sext_extract_le4 : forall v : word, sext 64 (bv_extract 0 32 (le_bytes_to_word (le4 v))) = sx32 v.
Proof.
  intros. rewrite sext_small. unfold sx32. f_equal. Local Ltac2 Set LiaHints.tbl := fun () => "0010=30228712271.1000001S".
rewrite signed_of_extract by lia. rewrite le_bytes_to_word_le4.
  unfold bv_swrap. f_equal. unfold bv_wrap, bv_modulus. change (Z.of_N 32) with 32%Z. rewrite Zplus_mod_idemp_l. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma sext_extract_le2 : forall v : word, sext 64 (bv_extract 0 16 (le_bytes_to_word (le2 v))) = sx16 v.
Proof.
  intros. rewrite sext_small. unfold sx16. f_equal. Local Ltac2 Set LiaHints.tbl := fun () => "0010=30228712271.1000001S".
rewrite signed_of_extract by lia. rewrite le_bytes_to_word_le2.
  unfold bv_swrap. f_equal. unfold bv_wrap, bv_modulus. change (Z.of_N 16) with 16%Z. rewrite Zplus_mod_idemp_l. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma sext_extract_le1 : forall v : word, sext 64 (bv_extract 0 8 (le_bytes_to_word (le1 v))) = sx8 v.
Proof.
  intros. rewrite sext_small. unfold sx8. f_equal. Local Ltac2 Set LiaHints.tbl := fun () => "0010=30228712271.1000001S".
rewrite signed_of_extract by lia. rewrite le_bytes_to_word_le1.
  unfold bv_swrap. f_equal. unfold bv_wrap, bv_modulus. change (Z.of_N 8) with 8%Z. rewrite Zplus_mod_idemp_l. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma zext_extract_byte : forall b : byte, zext 64 (bv_extract 0 8 (le_bytes_to_word [b])) = zxb b.
Proof.
  intros. rewrite zext_small. unfold zxb. f_equal. Local Ltac2 Set LiaHints.tbl := fun () => "0020=15377875376.230228382043.1000003004S1HS".
rewrite extract_low_mod by lia. rewrite le_bytes_to_word_byte.
  apply Z.mod_small. pose proof (bv_unsigned_in_range 8 b). unfold bv_modulus in *. change (Z.of_N 8) with 8%Z in *. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma sext_extract_byte : forall b : byte, sext 64 (bv_extract 0 8 (le_bytes_to_word [b])) = sxb b.
Proof.
  intros. rewrite sext_small. unfold sxb. f_equal. Local Ltac2 Set LiaHints.tbl := fun () => "0010=30228382043.1000001S".
rewrite signed_of_extract by lia. rewrite le_bytes_to_word_byte.
  reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma le1_zxb : forall b : byte, le1 (zxb b) = [b].
Proof.
  intros. unfold le1, zxb. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
  pose proof (bv_unsigned_in_range 8 b). unfold bv_modulus in H.
  Local Ltac2 Set LiaHints.tbl := fun () => "0010=30354061808.2000003S1H".
rewrite !Z_to_bv_unsigned, (bv_wrap_small 64) by (unfold bv_modulus; lia).
  apply bv_wrap_small. unfold bv_modulus; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
