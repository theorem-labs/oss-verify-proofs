(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Bytes.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import StrFun.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg.
Import ListNotations.
Open Scope bv_scope.

Definition memchr_entry := 0x1b77c%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ZFacts.
  Open Scope Z_scope.
  #[using="Type"] Lemma lxor_lt_256 : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lxor a b < 256.
  Proof.
    intros a b Ha Hb. pose proof (Z.lxor_nonneg a b) as Hnn. Local Ltac2 Set LiaHints.tbl := fun () => "00<0=18430926064.526980962951.826985714323.637910941582.857027251738.961885900550.661889472274.963370422384.663374621462.763469568193.99664605798.5 9664605810.6 00000100B00F00J00S00W00h00i00j00n01901HSS2Ha2Hb3Hnn3Hnz1nS2HaS2HaS2Hl1H2H0S2HbS2Ha2Hb3Hnn3Hnz1nSSS2HbS2Ha2Hb3HnnS2Ha2Hb3Hnn3Hnz".
split; [lia|].
    destruct (Z.eq_dec (Z.lxor a b) 0) as [->|Hnz]; [lia|].
    apply (proj2 (Z.log2_lt_pow2 (Z.lxor a b) 8 ltac:(lia))).
    pose proof (Z.log2_lxor a b ltac:(lia) ltac:(lia)) as Hl.
    assert (Z.log2 a < 8). { destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
    assert (Z.log2 b < 8). { destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
    lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  #[using="Type"] Lemma lxor_split : forall x y x' y', 0 <= x < 256 -> 0 <= x' < 256 -> 0 <= y -> 0 <= y' ->
    Z.lxor (x + 256 * y) (x' + 256 * y') = Z.lxor x x' + 256 * Z.lxor y y'.
  Proof.
    intros x y x' y' Hx Hx' Hy Hy'.
    pose proof (lxor_lt_256 x x' Hx Hx') as Hl.
    apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, !testbit_split by lia.
    destruct (i <? 8); rewrite Z.lxor_spec; reflexivity.
  Qed.

  #[using="Type"] Lemma le_val_nonneg : forall bs, bytes_ok bs -> 0 <= le_val bs.
  Proof. intros bs H. pose proof (le_val_range bs H). Local Ltac2 Set LiaHints.tbl := fun () => "0010=68399269389.3000004S2H0".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  #[using="Type"] Lemma le_val_xor_bcast : forall bs c, bytes_ok bs -> 0 <= c < 256 ->
    Z.lxor (le_val bs) (c * ones (length bs)) = le_val (map (fun b => Z.lxor b c) bs).
  Proof.
    induction bs as [|b bs IH]; intros c Hok Hc.
    - cbn. rewrite Z.mul_0_r. reflexivity.
    - inversion Hok as [|b0 bs0 Hb Hbs]; subst. cbn [le_val ones length map].
      Local Ltac2 Set LiaHints.tbl := fun () => "0080=15045551303.116022133226.32907290815.8 29268184279.833682125575.83746522746.8 38838733150.868397182792.800000100600700800900=00A00BSS3IHnFSFS2HcS2HbF".
replace (c * (1 + 256 * ones (length bs))) with (c + 256 * (c * ones (length bs))) by lia.
      rewrite lxor_split; try lia.
      + rewrite IH by assumption. reflexivity.
      + apply le_val_nonneg. exact Hbs.
      + pose proof (le_val_range (repeat 1 (length bs))) as Hr. assert (0 <= ones (length bs)); [|nia].
        clear. induction (length bs); cbn; lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  #[using="Type"] Lemma bytes_ok_xor : forall bs c, bytes_ok bs -> 0 <= c < 256 -> bytes_ok (map (fun b => Z.lxor b c) bs).
  Proof.
    intros bs c H Hc. unfold bytes_ok in *. rewrite Forall_map. eapply Forall_impl; [|exact H].
    intros b Hb. apply lxor_lt_256; assumption.
  Qed.

  #[using="Type"] Lemma In0_xor : forall bs c, In 0 (map (fun b => Z.lxor b c) bs) <-> In c bs.
  Proof.
    intros bs c. rewrite in_map_iff. split.
    - intros (b & Hb & Hin). apply Z.lxor_eq in Hb. subst. exact Hin.
    - intros Hin. exists c. split; [apply Z.lxor_nilpotent| exact Hin].
  Qed.
End ZFacts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition memchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (buf : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (memchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf))
                 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ bytes_at usegs m' (bv_unsigned a0) buf.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf : list byte).
  Hypothesis MI : mem_inv usegs m.
  Hypothesis BUF : bytes_at usegs m (bv_unsigned a0) buf.
  Hypothesis OK : memchr_ok (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf.
  Let MU : munch [] m m := munch_refl [] m.
  Let WM : wmono usegs m m := wmono_refl usegs m.

  Notation A := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation c := ((bv_unsigned a1) mod 256)%Z.
  Notation len := (Z.of_nat (length buf)).
  Notation POST := (memchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 buf m).
  (* [comment removed for export] *)
  Notation ST pc x5 x10 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 x10 (Z_to_bv 64 c) x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).
  Notation CMAGIC := 72340172838076672%Z.      (* [comment removed for export] *)
  Notation HIGHS := 9259542123273814144%Z.     (* [comment removed for export] *)
  Notation ONES := 72340172838076673%Z.       (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition NOB (i : Z) : Prop :=
    forall j b, (j < Z.to_nat i)%nat -> nth_error buf j = Some b -> bv_unsigned b <> c.

  #[using="m BUF"] Lemma A_bound : (0 <= A /\ A + len <= 2^64 /\ 0 <= n < 2^64 /\ 0 <= c < 256)%Z.
  Proof.
    pose proof (bytes_at_bound _ _ _ _ BUF).
    pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R.
    pose proof (Z.mod_pos_bound (bv_unsigned a1) 256). cbn. Local Ltac2 Set LiaHints.tbl := fun () => "0010=5421605207.43000005S1H1R".
lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  #[using="Type"] Lemma NOB_0 : NOB 0.
  Proof. intros j b Hj. cbn in Hj. Local Ltac2 Set LiaHints.tbl := fun () => "0010>64887945465.43000004S2Hj".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  #[using="Type"] Lemma NOB_S : forall i b, (0 <= i)%Z -> NOB i -> nth_error buf (Z.to_nat i) = Some b -> bv_unsigned b <> c -> NOB (i + 1).
  Proof.
    intros i b Hi H Hn Hb j b' Hj Hn'.
    destruct (Nat.eq_dec j (Z.to_nat i)) as [->|NE]. { rewrite Hn in Hn'. injection Hn' as <-. exact Hb. }
    eapply H; [|exact Hn']. Local Ltac2 Set LiaHints.tbl := fun () => "0010>57898514806.5100000:S2Hi2Hj2NE".
lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="OK"] Lemma ok_cases :
    (exists j b, Z.of_nat j < n /\ nth_error buf j = Some b /\ bv_unsigned b = c /\
       (forall j' b', (j' < j)%nat -> nth_error buf j' = Some b' -> bv_unsigned b' <> c) /\
       (n <= len \/ Z.of_nat j + 1 + (- (A + Z.of_nat j + 1)) mod 8 <= len))%Z
    \/ ((forall j b, (Z.of_nat j < n)%Z -> nth_error buf j = Some b -> bv_unsigned b <> c) /\ (n <= len)%Z).
  Proof.
    pose proof OK as H. unfold memchr_ok in H.
    destruct (find_byte c (firstn (Z.to_nat n) buf)) as [j|] eqn:FB.
    - left. destruct (find_byte_Some _ _ _ FB) as (Hl & (b & Hn & Hb) & Hmin).
      rewrite firstn_length in Hl.
      rewrite nth_error_firstn in Hn. Local Ltac2 Set LiaHints.tbl := fun () => "0050>15185597435.4819627795454.4840197994312.5265404663426.4665408857090.4800000400500=00A00ES2HlFS2Hl3Hj'S2HjS2Hl".
replace (Nat.ltb j (Z.to_nat n)) with true in Hn by (symmetry; apply Nat.ltb_lt; lia).
      exists j, b. repeat split; try assumption; try lia.
      intros j' b' Hj' Hn'. eapply Hmin; [exact Hj'|]. rewrite nth_error_firstn.
      replace (Nat.ltb j' (Z.to_nat n)) with true by (symmetry; apply Nat.ltb_lt; lia). exact Hn'.
    - right. split; [|exact H]. intros j b Hj Hn. eapply (find_byte_None _ _ FB j). rewrite nth_error_firstn.
      replace (Nat.ltb j (Z.to_nat n)) with true by (symmetry; apply Nat.ltb_lt; lia). exact Hn.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  #[using="a0 OK"] Lemma readable : forall i, (0 <= i < n)%Z -> NOB i -> exists b, nth_error buf (Z.to_nat i) = Some b.
  Proof.
    intros i Hi HN. destruct (nth_error buf (Z.to_nat i)) as [b|] eqn:E; [exists b; reflexivity|].
    exfalso. apply nth_error_None in E.
    Local Ltac2 Set LiaHints.tbl := fun () => "0020>59310683140.5259321168653.4600000900DS1E1H3HgeS2Hi1E4Hlen".
destruct ok_cases as [(j & b & Hj & Hn & Hb & Hmin & _)|(Hall & Hlen)]; [|lia].
    pose proof (nth_error_lt _ _ _ Hn).
    destruct (Nat.lt_ge_cases j (Z.to_nat i)) as [Hlt|Hge]; [|lia].
    exact (HN _ _ Hlt Hn Hb).
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  #[using="OK"] Lemma readable8 : forall i, (0 <= i)%Z -> (i + 8 <= n)%Z -> ((A + i) mod 8 = 0)%Z -> NOB i ->
    (Z.to_nat i + 8 <= length buf)%nat.
  Proof.
    intros i Hi Hi8 Hal HN.
    Local Ltac2 Set LiaHints.tbl := fun () => "0040>41037755880.4741037757502.5541050332726.5541052435169.5400000=00T00^010S2Hi3Hi84HlenS2Hi3Hal3Hsl1H3Hge4Hlt8S1H3Hge2H0S2Hi3Hi83Hsl1H3Hge".
destruct ok_cases as [(j & b & Hj & Hn & Hb & Hmin & Hsl)|(Hall & Hlen)]; [|lia].
    pose proof (nth_error_lt _ _ _ Hn).
    destruct (Nat.lt_ge_cases j (Z.to_nat i)) as [Hlt|Hge]. { exfalso. exact (HN _ _ Hlt Hn Hb). }
    destruct Hsl as [Hsl|Hsl]; [lia|].
    destruct (Nat.lt_ge_cases j (Z.to_nat i + 8)) as [Hlt8|]; [|lia].
    OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  #[using="Type"] Lemma res_found : forall i b, (0 <= i < n)%Z -> NOB i -> nth_error buf (Z.to_nat i) = Some b -> bv_unsigned b = c ->
    memchr_res A c n buf = (A + i)%Z.
  Proof.
    intros i b Hi HN Hn Hb. unfold memchr_res.
    Local Ltac2 Set LiaHints.tbl := fun () => "0020>25610351451.4647399679485.46000004008S2HiS2Hi".
rewrite (find_byte_charact c _ (Z.to_nat i) b); [lia| | exact Hb|].
    - rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia). exact Hn.
    - intros j b' Hj Hn'. rewrite nth_error_firstn in Hn'. destruct (Nat.ltb j (Z.to_nat n)); [|discriminate].
      exact (HN _ _ Hj Hn').
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  #[using="Type"] Lemma res_none : NOB n -> memchr_res A c n buf = 0%Z.
  Proof.
    intros HN. unfold memchr_res. rewrite find_byte_None_intro; [reflexivity|].
    intros j b Hn. rewrite nth_error_firstn in Hn. destruct (Nat.ltb_spec0 j (Z.to_nat n)); [|discriminate].
    Local Ltac2 Set LiaHints.tbl := fun () => "0010>65397782400.45000003S1l".
exact (HN j b ltac:(lia) Hn).
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="MI BUF OK MU WM"] Lemma memchr_tail : forall (k : nat) (i : Z) (x5 x12 x14 x15 x16 x17 : word),
    Z.to_nat (n - i) = k -> (0 <= i < n)%Z -> NOB i ->
    evt usegs POST (ST 0x1b81c x5 (Z_to_bv 64 (A + i)) x12 (Z_to_bv 64 (n - i)) x14 x15 x16 x17).
  Proof.
    Local Ltac2 Set LiaHints.tbl := fun () => "00;0>10351558129.5910357883337.5612527845977.5913714643354.5919252948495.5824985903395.5933987028406.514323788002.59 48489401994.5952067443862.5968131637099.5900000900B00N00W00]00^00e00k01101=01IS2Hk2Hi1HS2Hk2Hi1HS2Hk2Hi1H2K0S2Hk2Hi1HS2Hk1HFS2Hk2HiS2Hk1HS2Hk1HS2Hk2Hi2AB1HS2Hk2Hi1H2K0".
induction k as [|k IH]; intros i x5 x12 x14 x15 x16 x17 Hk Hi HN; pose proof A_bound as AB; [lia|].
    destruct (readable i Hi HN) as [b Hn]. pose proof (nth_error_lt _ _ _ Hn).
    pose proof (u8ro_read usegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD.
    zstep. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *) zstep. rewrite <- (res_found i b Hi HN Hn K). finish.
    - zstep. zstep. zstep. if_cases K0; zify_cond K0.
      + replace (n - i + -1)%Z with (n - (i + 1))%Z by lia. replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
        apply (IH (i + 1)%Z); try lia. eapply NOB_S; eauto; lia.
      + (* [comment removed for export] *) zstep. zstep. rewrite <- res_none at 1. { finish. }
        replace n with (i + 1)%Z by lia. eapply NOB_S; eauto; lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="MI BUF OK MU WM"] Lemma memchr_tail_entry : forall (i : Z) (x5 x13 x14 x15 x16 x17 : word),
    (0 <= i <= n)%Z -> NOB i ->
    evt usegs POST (ST 0x1b814 x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) x13 x14 x15 x16 x17).
  Proof.
    intros i x5 x13 x14 x15 x16 x17 Hi HN; pose proof A_bound as AB.
    zstep. zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0050>17162713045.5119659927144.5121320089685.5144205152421.5167959291519.5100000100700>00?00ESS2Hi1KS2Hi2ABFS2Hi1K".
if_cases K; zify_cond K.
    - zstep. zstep. rewrite <- res_none at 1. { finish. } replace n with i by lia. exact HN.
    - apply (memchr_tail (Z.to_nat (n - i)) i); lia || assumption.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="MI BUF OK MU WM"] Lemma memchr_words : forall (k : nat) (i : Z) (x5 x17 : word),
    Z.to_nat (n - i) = k -> (0 <= i)%Z -> (i + 8 <= n)%Z -> ((A + i) mod 8 = 0)%Z -> NOB i ->
    evt usegs POST (ST 0x1b7f0 x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) (Z_to_bv 64 CMAGIC) (Z_to_bv 64 HIGHS)
                       (Z_to_bv 64 (c * ONES)) (Z_to_bv 64 7) x17).
  Proof.
    induction k as [k IH] using lt_wf_ind; intros i x5 x17 Hk Hi Hi8 Hal HN; pose proof A_bound as AB.
    pose proof (readable8 i Hi Hi8 Hal HN) as HW.
    Local Ltac2 Set LiaHints.tbl := fun () => "00S0>10351593816.5210351596207.5912527855379.6215268711778.6015394470183.6315515322590.6019259242976.6119657832839.6119658072567.5719843526159.5824985896041.6226074862654.6034887345828.6534887345829.6434887345830.6334887345834.6737116517670.6037116525668.6237817653656.6040155451754.6040906143099.604323795368.62 45146448498.6048489409472.6252067434972.6253024982923.6355653127761.6057380559801.5757380576185.5657382343718.5859308637593.6259586081466.6761252241053.538526918906.63 8949003020.60 00000:00G00X00b01=01U01_02002A02K02L02`03403H03\04004:04D04U04_04`04j05705A05U06006A06N06[06h07907C07T07U07bS2Hk2Hi2HWS2Hk2Hi2HW2CLS2Hk2Hi3Hi82HW2CLS2Hk2HW2CLS2Hk2Hi3Hi82AB2HW2CL2Hj3HgeS2Hk2Hi3Hi83Hal2AB2HW2CLS2Hk2HW2CLS2Hk2Hi3Hi82HW2CLS2Hk2Hi3Hi82HW2CLS2Hk2HW2CLFS2Hk2Hi3Hi82AB2HW2CLS2Hk2Hi3Hi82AB2HW2CLS2Hk2Hi3Hi82AB2HW2CLS2Hk2Hi3Hi82AB2HW2CLS2Hk2Hi3Hi82AB2HW2CLS2Hk2HW2CLS2Hk2HW2CLS2Hk3Hi82HW2CL2K8S2Hk2HW2CLFS2Hk2HW2CLS2Hk2Hi2HW2CLS2Hk2HW2CLS2Hk2Hi3Hi82AB2HW2CLS2Hk2Hi3Hi82AB2HW2CL2Hj3HgeS2Hk2Hi3Hi82HW2CLS2Hk2AB2HW2CLS2Hk2AB2HW2CLS2Hk2AB2HW2CLS2Hk3Hi82HW2CL2KzS2Hk2HW2CLS2Hk2Hi3Hi82AB2HWFS2Hk2HW2CL2K8".
pose proof (bytes_at_read usegs m A buf i 8 BUF ltac:(lia) HW) as RD.
    set (chunk := firstn 8 (skipn (Z.to_nat i) buf)) in RD.
    assert (CL : length chunk = 8%nat). { subst chunk. rewrite firstn_length, skipn_length. lia. }
    pose proof (le_val_range _ (bytes_ok_map chunk)) as WR. rewrite length_map, CL in WR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR.
    pose proof (le_val_range _ (bytes_ok_xor _ c (bytes_ok_map chunk) ltac:(lia))) as XR. rewrite !length_map, CL in XR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in XR.
    do 6 zstep.
    rewrite (load8_le_val chunk CL).
    replace (Z.lxor (le_val (map bv_unsigned chunk)) (c * ONES)) with (le_val (map (fun b => Z.lxor b c) (map bv_unsigned chunk))).
    2:{ change ONES with ONES64b. rewrite <- ones_8, <- CL, <- (length_map bv_unsigned). symmetry. apply le_val_xor_bcast; [apply bytes_ok_map| lia]. }
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      clear K. destruct (readable i ltac:(lia) HN) as [b Hn].
      pose proof (u8ro_read usegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD1.
      zstep. zstep. zstep. if_cases Kb; zify_cond Kb.
      + zstep. zstep. zstep. if_cases Kz; zify_cond Kz; [|exfalso; lia].
        replace (n - i + -1)%Z with (n - (i + 1))%Z by lia. replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
        apply (memchr_tail (Z.to_nat (n - (i + 1))) (i + 1)); try lia. eapply NOB_S; eauto; lia.
      + zstep. zstep. rewrite <- (res_found i b ltac:(lia) HN Hn Kb). finish.
    - apply (haszero64_clang _ (bytes_ok_xor _ c (bytes_ok_map chunk) ltac:(lia)) ltac:(rewrite !length_map; exact CL)) in K.
      rewrite In0_xor in K.
      (* [comment removed for export] *)
      assert (HN8 : NOB (i + 8)).
      { intros j b Hj Hn. destruct (Nat.lt_ge_cases j (Z.to_nat i)) as [Hlt|Hge]. { exact (HN _ _ Hlt Hn). }
        intros Hb. apply K. rewrite <- Hb. apply in_map. subst chunk.
        apply nth_error_In with (n := (j - Z.to_nat i)%nat).
        rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
        rewrite nth_error_skipn, <- Hn. f_equal. lia. }
      zstep. zstep. zstep. if_cases K8; zify_cond K8.
      + replace (A + i + 8)%Z with (A + (i + 8))%Z by lia. replace (n - i + -8)%Z with (n - (i + 8))%Z by lia.
        apply (IH (Z.to_nat (n - (i + 8)))); try lia; try exact HN8. all: OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
      + replace (A + i + 8)%Z with (A + (i + 8))%Z by lia. replace (n - i + -8)%Z with (n - (i + 8))%Z by lia.
        apply (memchr_tail_entry (i + 8)); try lia; exact HN8.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="MI BUF OK MU WM"] Lemma memchr_mid : forall (i : Z) (x5 x13 x14 x15 x16 x17 : word),
    (0 <= i <= n)%Z -> NOB i -> ((bv_unsigned x14 = 0)%Z <-> i = n) -> (i = n \/ (A + i) mod 8 = 0)%Z ->
    evt usegs POST (ST 0x1b7c0 x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) x13 x14 x15 x16 x17).
  Proof.
    intros i x5 x13 x14 x15 x16 x17 Hi HN H14 Hal; pose proof A_bound as AB.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *) apply H14 in K. subst i. zstep. zstep. rewrite <- res_none at 1; [finish| exact HN].
    - assert (Hin : (i < n)%Z). { Local Ltac2 Set LiaHints.tbl := fun () => "00B0>10351557113.5910351596207.5612676437361.6717156410720.5919251557044.6719259242976.5819655720203.5419657823453.5919657832839.5821318007520.5925479885546.6744203057680.5946995586026.6754829261425.6757073375597.5960490645209.5960859686622.548132486653.54 00000400800900:00;00<00D00H00L00S00T00U00V00W00[00`00l013S2HiS2HiSSSSS2Hi3HinS2HiS2HiS2Hi2ABSFSSS2K8S3HalS2Hi3H141K1nS1H3Hin".
destruct (Z.eq_dec i n) as [E|]; [|lia]. exfalso. apply K. apply H14. exact E. }
      destruct Hal as [|Hal]; [lia|].
      destruct (readable i ltac:(lia) HN) as [b Hn].
      pose proof (u8ro_read usegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD.
      zstep. zstep. if_cases Kb; zify_cond Kb.
      + apply memchr_tail_entry; [lia| exact HN].
      + zstep. zstep. if_cases K8; zify_cond K8.
        * apply memchr_tail_entry; [lia| exact HN].
        * do 7 zstep.
          apply (memchr_words (Z.to_nat (n - i)) i); try lia. exact HN.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  #[using="a1"] Lemma b2z_word_zero_iff : forall t, bv_unsigned (Z_to_bv 64 (Z.b2z t)) = 0%Z <-> t = false.
  Proof. intros t. Local Ltac2 Set LiaHints.tbl := fun () => "0020>52513816717.4053518944813.40000001002SS".
rewrite unsigned_lit by (destruct t; cbn; lia). destruct t; cbn; split; intros; first [congruence | lia]. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="MI BUF OK MU WM"] Lemma memchr_head : forall (k : nat) (i : Z) (x5 x13 x14 x17 : word),
    Z.to_nat (n - i) = k -> (0 <= i < n)%Z -> NOB i -> ((A + i) mod 8 <> 0)%Z ->
    evt usegs POST (ST 0x1b798 x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) x13 x14 (Z_to_bv 64 (A + i + 1)) (Z_to_bv 64 1) x17).
  Proof.
    Local Ltac2 Set LiaHints.tbl := fun () => "00Q0>10351547555.5710357883337.5512525759365.5912527846362.6013714642969.6014382650609.6014384757934.5915517426954.5917156415546.5719259242976.5719620497060.6619657832839.5721318008683.6024984669806.5924985903264.6024987994367.5929784417117.5929786562013.5831693996101.6031696103450.5933491990773.6033494077610.604321701182.59 4323788129.60 43657776012.5044203052874.5748487311190.5948489402121.6052076332703.6753510313883.67654645427.59  656748780.60  8922889132.60 00000900B00K00W00`00l00m01>01D01J01K01T01`01f01g01h01n02402502602J02K02Q02W02^02_02e02k03703=03I03U03[S2Hk2Hi1HS2Hk2Hi1HS2Hk2Hi1HS2Hk2Hi1H2K1S2Hk2Hi1HS2Hk2Hi1H2K1FS2Hk2Hi3Hal1H3KalS2Hk1HS2Hk1HFS2Hk2Hi1HS2Hk2Hi2AB1HS2Hk1HFFS2Hk1HS2Hk1HFFS2Hk2Hi3Hal1H2K13KalFS2Hk1HS2Hk1HS2Hk2HiFS2Hk1HS2Hk1HS2Hk2Hi2AB1HS2Hk1HS2Hk2Hi2AB1HS2Hk2Hi1H2K1S2Hk1H".
induction k as [|k IH]; intros i x5 x13 x14 x17 Hk Hi HN Hal; pose proof A_bound as AB; [lia|].
    destruct (readable i Hi HN) as [b Hn]. pose proof (nth_error_lt _ _ _ Hn).
    pose proof (u8ro_read usegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD.
    zstep. zstep. zstep. if_cases Kb; zify_cond Kb.
    - (* [comment removed for export] *) apply (memchr_tail (Z.to_nat (n - i)) i); try lia. exact HN.
    - pose proof (NOB_S i b ltac:(lia) HN Hn Kb) as HN1.
      zstep. zstep. zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
      + replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. replace (n - i + -1)%Z with (n - (i + 1))%Z by lia.
        apply (memchr_mid (i + 1)); try lia; try exact HN1.
        * rewrite b2z_word_zero_iff, Z.ltb_ge. lia.
        * right. revert Kal. zb_masks. intros Kal. OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
      + zstep. zstep. if_cases K1; zify_cond K1.
        * replace (A + i + 2)%Z with (A + (i + 1) + 1)%Z by lia.
          replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. replace (n - i + -1)%Z with (n - (i + 1))%Z by lia.
          apply (IH (i + 1)%Z); try lia; try exact HN1. revert Kal. zb_masks. intros Kal. OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
        * replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. replace (n - i + -1)%Z with (n - (i + 1))%Z by lia.
          apply (memchr_mid (i + 1)); try lia; try exact HN1. rewrite b2z_word_zero_iff, Z.ltb_ge. lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="MI BUF OK MU WM"] Lemma memchr_body :
    evt usegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1b77c) fc None m (seg_rom usegs)).
  Proof.
    pose proof A_bound as AB. pose proof (zr_word a1) as R1. unfold inr64 in R1.
    zstep. replace (Z.land (bv_unsigned a1) 255) with c.
    2:{ change 255%Z with (2^8 - 1)%Z. Local Ltac2 Set LiaHints.tbl := fun () => "00A0>10230559015.4424984669806.4329784416990.4329784564573.4233494077737.4438702289770.4438704396982.4339205877143.4339207967819.4443547111901.4343549202433.4452157936534.4352160027210.4453510313883.5161401189938.4361403293678.4463368414893.4200000400500600700800?00F00G00H00L00S00T00[00\00]00^00_S2R1SSSFS2AB2K0S2AB2R1FFS2ABS2AB2K0FS2AB2K0SFFS".
rewrite zb_land_mask by lia. reflexivity. }
    zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
    - (* [comment removed for export] *)
      eapply evt_eq.
      2:{ apply (memchr_mid 0 t0 (Z_to_bv 64 (Z.land A 7)) (Z_to_bv 64 (Z.b2z (0 <? n)%Z)) a5 a6 a7); try lia.
          - apply NOB_0. - rewrite b2z_word_zero_iff, Z.ltb_ge. lia.
          - right. revert Kal. zb_masks. intros Kal. rewrite Z.add_0_r. exact Kal. }
      unfold mkR. rewrite Z_to_bv_plus0, Z.sub_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - zstep. if_cases K0; zify_cond K0.
      + (* [comment removed for export] *)
        eapply evt_eq.
        2:{ apply (memchr_mid 0 t0 (Z_to_bv 64 (Z.land A 7)) (Z_to_bv 64 (Z.b2z (0 <? n)%Z)) a5 a6 a7); try lia.
            - apply NOB_0. - rewrite b2z_word_zero_iff, Z.ltb_ge. lia. }
        unfold mkR. rewrite Z_to_bv_plus0, Z.sub_0_r, Z_to_bv_bv_unsigned. reflexivity.
      + zstep. zstep.
        eapply evt_eq.
        2:{ apply (memchr_head (Z.to_nat n) 0 t0 (Z_to_bv 64 (Z.land A 7)) (Z_to_bv 64 (Z.b2z (0 <? n)%Z)) a7); try lia.
            - apply NOB_0. - revert Kal. zb_masks. intros Kal. rewrite Z.add_0_r. exact Kal. }
        unfold mkR. rewrite Z_to_bv_plus0, Z.sub_0_r, Z_to_bv_bv_unsigned, Z.add_0_r. reflexivity.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Proofs.

Lemma memchr_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (buf : list byte),
  bytes_at usegs m (bv_unsigned a0) buf ->
  memchr_ok (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf ->
  mem_inv usegs m ->
  evt usegs (memchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 buf m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b77c) fc None m (seg_rom usegs)).
Proof. intros until buf. intros BUF OK MI. apply memchr_body; assumption. Qed.
