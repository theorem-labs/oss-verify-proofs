(* The adapter between THIS tree's runtime contracts (lib/A/Rt/RtDefs.v: ecall_pre_stk, aread_ok, awrite_ok,
   astr_at, atail_vis, aguard_ok, rt_rom_view) and the premises the relocated bridge asks for (lib/A/Rt/RtBzHBase.v
   ecall_pre_k, rom_viewN / rom_viewO; lib/A/Bz: Mem.bytes_at, Frame.stk, I_qck.chk_ok, Step.ro_cells). It is the
   part of the five lifts that does not depend on which entry is walked; the per-entry glue is in RtL*.v.

   What each piece closes (of the gaps measured between the relocated bridge and our contracts):
   - G1, the pre vocabulary: ecall_pre_k's `alloc_ceiling <= ly_stk_lo ly` is a layout fact of every AR
     (YG0f.v:339 lo_stk_ceil), so our ecall_pre_stk gives the bridge's ecall_pre_k (pre_k_of_stk). The strings of
     our contracts are astr_at + aread_ok + atail_vis, which give the walks' bytes_at, their slack after the
     terminator (G4), and their separation from the callee's stack window.
   - G2, rom_viewO: our contracts carry rt_rom_view, which is rom_viewN; the owned read-only bytes of this image
     are pinned by the constant table of the per-binary record (A/AF0m.v Tfib_const_abs, whose header says so), so
     rom_viewO follows from AR by one computation over the 5,012 owned read-only bytes (RtBzPins.v,
     rom_viewO_of_ARm below).
   - the range check: chk_ok's acc and qc_words come from aread_ok through RtBzStr; its rng_ok asks region_in_mem,
     which is the contracts' own `amem_range p (len + 8)` on each checked string (chk_of_read). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YK04 YK0i YK14 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI00 YI04 YK06 YM05.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1v AF0m AF0x AE2y.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs RtBzHBase RtBzPins.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtBzStr RtBzBridge RtBzClean RtBzPre.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib.ImageA.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib.Mem.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib.Frame.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib.Cells.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib.Step.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.Shadow.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.R_m2s.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_consts.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_qck.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module BI := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib.ImageA.
Module BM := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib.Mem.
Module BF := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib.Frame.
Module BC := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib.Cells.
Module BS := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib.Step.
Module BSh := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.Shadow.
Module BR := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.R_m2s.
Module BK := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_consts.
Module BQ := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_qck.

(* the owned read-only bytes and the cells that pin them: RtBzPins.v (one computation) *)

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* ---- G1: the stack premise ---- *)

Lemma pre_k_of_stk : forall stk ly S (W : world tfibsegs) regs mem md,
  ecall_pre_stk tfibsegs B stk ly S W regs mem md ->
  ecall_pre_k tfibsegs B stk ly S W regs mem md.
Proof.
  intros stk ly S W regs mem md (HEP & Hlo & Hpres).
  pose proof HEP as (HAR & _).
  split; [exact HEP|].
  split; [|split; [exact Hlo | intros a Ha; exact (Hpres a Ha)]].
  pose proof (lo_stk_ceil ly (am_layout B ly S _ (proj1 HAR))) as H. unfold ASAN_CEIL in H. exact H.
Qed.

(* the callee's stack window, on the real store and on the cleaned one *)
Lemma stk_of_stk_pre : forall stk ly S (W : world tfibsegs) regs mem md,
  ecall_pre_stk tfibsegs B stk ly S W regs mem md -> 0 <= stk ->
  BF.stk BI.asegs (mrestrict (w_H W) mem) (spZ regs - stk) (spZ regs) /\
  0x7fff7f800000 <= alloc_ceiling /\ alloc_ceiling <= spZ regs - stk /\ spZ regs <= 2 ^ 47.
Proof.
  intros stk ly S W regs mem md HPRE Hs.
  exact (RtBzPre.stk_of_pre B ly S W regs mem md stk (pre_k_of_stk stk ly S W regs mem md HPRE) Hs).
Qed.

(* ---- G2: the read-only views ---- *)

Lemma romN_of_rt : forall (W : world tfibsegs) mem,
  rt_rom_view tfibsegs B W mem -> rom_viewN tfibsegs B W mem.
Proof. intros W mem H a H1 H2 H3. exact (H a H1 H2 H3). Qed.

Section o.
Hypothesis TB : SegBSyms B.

Lemma rom_viewO_of_ARm : forall ly S (W : world tfibsegs) mem,
  ARm B ly S (aview tfibsegs (w_H W) mem) -> rom_viewO tfibsegs B W mem.
Proof.
  intros ly S W mem M a Hrom Hown.
  (* the byte lies in an owned range and in a read-only segment, so in one of owned_ro's ranges *)
  rewrite (ts_owned B TB) in Hown. apply Exists_exists in Hown as (r & Hinr & Hzr).
  destruct Hrom as (sg & Hinsg & Hwr & Hlo & Hhi).
  assert (HP : pins_in Tfib_const_abs a = true).
  { apply (pins_of_ranges Tfib_const_abs owned_ro a owned_ro_pinned). apply Exists_exists.
    exists (zisect r (seg_zr sg)). split.
    - exact (in_owned_ro r sg Hinr Hinsg Hwr).
    - unfold in_zr, zisect, seg_zr, in_zr in *. cbn [fst snd] in *. lia. }
  (* the pin: a constant cell of the record holds the image's byte there *)
  unfold pins_in in HP. destruct (img_byte a) as [ib|] eqn:EI; [|discriminate].
  apply existsb_exists in HP as (c & Hinc & Hpin).
  unfold pin_cell in Hpin.
  destruct (c_at c) as [ca| | | | | | | | | | | | | | | | | |] eqn:EA; try discriminate.
  destruct (c_val c) as [e|mask vv] eqn:EV; [|discriminate].
  destruct e as [v| | | | | | | | | | | | | | | | | |]; try discriminate.
  destruct ((ca <=? a) && (a <? ca + Z.of_nat (c_w c)))%bool eqn:Hrng; [|discriminate].
  apply andb_prop in Hrng as (Hle & Hlt).
  apply Z.leb_le in Hle. apply Z.ltb_lt in Hlt. apply Z.eqb_eq in Hpin.
  (* AR holds every constant cell *)
  assert (HC : cell_holds B ly (aview tfibsegs (w_H W) mem) c).
  { apply (proj1 (Forall_forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly))
            (am_const B ly S _ M)).
    rewrite (ts_const B TB ly). unfold Tfib_const.
    apply in_or_app. right. apply in_or_app. left. exact Hinc. }
  unfold cell_holds in HC. rewrite EA, EV in HC. cbn [aeval] in HC.
  specialize (HC (Z.to_nat (a - ca)) ltac:(lia)).
  rewrite Z2Nat.id in HC by lia. replace (ca + (a - ca)) with a in HC by lia.
  rewrite HC, Hpin. unfold img_byte in EI. symmetry. exact EI.
Qed.

Lemma rom_eq_of_rt : forall ly S (W : world tfibsegs) mem md,
  AR tfibsegs B ly S W mem md -> rt_rom_view tfibsegs B W mem ->
  RtBzClean.rom_eq (mrestrict (w_H W) mem).
Proof.
  intros ly S W mem md HAR HR.
  exact (RtBzClean.rom_eq_of_views B W mem TB (romN_of_rt W mem HR)
           (rom_viewO_of_ARm ly S W mem (proj1 HAR))).
Qed.

End o.

(* ---- bytes: our byte lists as the walks read them ---- *)

Lemma bz_bytes_of_abytes : forall (W : world tfibsegs) mem a (l : list byte),
  abytes_at tfibsegs W mem a l -> 0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
  BM.bytes_at BI.asegs (mrestrict (w_H W) mem) a l.
Proof.
  intros W mem a l HB Ha Hl. split; [exact Ha|]. split; [exact Hl|].
  intros i Hi. specialize (HB i Hi). unfold aview in HB.
  rewrite <- RtBzPre.mrd_mbyte in HB.
  destruct (BM.mrd BI.asegs (mrestrict (w_H W) mem) (BM.wa (a + Z.of_nat i))) as [b|] eqn:E;
    [|cbn in HB; discriminate].
  cbn [option_map] in HB. injection HB as HB.
  rewrite (nth_error_nth' l (Z_to_bv 8 0) Hi). f_equal. apply bv_eq. exact HB.
Qed.

Lemma bz_str_bytes : forall (W : world tfibsegs) mem x (s : list byte),
  astr_at tfibsegs W mem x s -> 0 <= x -> x + astr_len s + 1 <= 2 ^ 64 ->
  BM.bytes_at BI.asegs (mrestrict (w_H W) mem) x (s ++ [Z_to_bv 8 0]).
Proof.
  intros W mem x s (HB & _) Hx Hl. apply bz_bytes_of_abytes; [exact HB | exact Hx |].
  rewrite length_app. cbn [length]. unfold astr_len in Hl. lia.
Qed.

(* ---- G4: the bytes a word-at-a-time loop reads past the terminator ---- *)

Definition tail_bytes (W : world tfibsegs) (mem : word -> option byte) (e : Z) : list byte :=
  map (fun j => match aview tfibsegs (w_H W) mem (e + 1 + Z.of_nat j) with
                | Some v => Z_to_bv 8 v
                | None => Z_to_bv 8 0
                end)
      (seq 0 (Z.to_nat (7 - e mod 8))).

Lemma tail_bytes_length : forall W mem e, Z.of_nat (length (tail_bytes W mem e)) = 7 - e mod 8.
Proof.
  intros W mem e. unfold tail_bytes. rewrite length_map, length_seq.
  pose proof (Z.mod_pos_bound e 8 ltac:(lia)). lia.
Qed.

Lemma mod_neg_succ : forall e, (- (e + 1)) mod 8 = 7 - e mod 8.
Proof. intros e. Z.div_mod_to_equations. lia. Qed.

Lemma bz_tail_bytes : forall (W : world tfibsegs) mem (e : Z),
  atail_vis tfibsegs W mem e -> 0 <= e -> e + 8 <= 2 ^ 64 ->
  BM.bytes_at BI.asegs (mrestrict (w_H W) mem) (e + 1) (tail_bytes W mem e).
Proof.
  intros W mem e HT He Hb.
  pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as Hm.
  split; [lia|]. split.
  - pose proof (tail_bytes_length W mem e). lia.
  - intros i Hi.
    assert (Hi' : Z.of_nat i < 7 - e mod 8)
      by (pose proof (tail_bytes_length W mem e); lia).
    assert (HV : aview tfibsegs (w_H W) mem (e + 1 + Z.of_nat i) <> None)
      by (apply HT; lia).
    destruct (aview tfibsegs (w_H W) mem (e + 1 + Z.of_nat i)) as [v|] eqn:EV;
      [|exfalso; exact (HV eq_refl)].
    unfold tail_bytes. rewrite nth_error_map, nth_error_seq.
    replace (i <? Z.to_nat (7 - e mod 8))%nat with true
      by (symmetry; apply Nat.ltb_lt; lia).
    cbn [option_map Nat.add].
    rewrite EV. cbn [option_map].
    unfold aview in EV. rewrite <- RtBzPre.mrd_mbyte in EV.
    destruct (BM.mrd BI.asegs (mrestrict (w_H W) mem) (BM.wa (e + 1 + Z.of_nat i))) as [b|] eqn:E;
      [|cbn in EV; discriminate].
    cbn [option_map] in EV. injection EV as EV. subst v.
    f_equal. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* the walks' `str ++ 0 :: slack` with slack long enough to fill the terminator's word *)
Lemma bz_str_slack : forall (W : world tfibsegs) mem x (s : list byte),
  astr_at tfibsegs W mem x s -> atail_vis tfibsegs W mem (x + astr_len s) ->
  0 <= x -> x + astr_len s + 8 <= 2 ^ 64 ->
  BM.bytes_at BI.asegs (mrestrict (w_H W) mem) x
    (s ++ Z_to_bv 8 0 :: tail_bytes W mem (x + astr_len s)) /\
  (- (x + astr_len s + 1)) mod 8 <= Z.of_nat (length (tail_bytes W mem (x + astr_len s))).
Proof.
  intros W mem x s HS HT Hx Hb. set (e := x + astr_len s) in *.
  pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as Hm.
  split.
  - replace (s ++ Z_to_bv 8 0 :: tail_bytes W mem e)
      with ((s ++ [Z_to_bv 8 0]) ++ tail_bytes W mem e)
      by (rewrite <- app_assoc; reflexivity).
    apply (proj2 (BM.bytes_at_app BI.asegs (mrestrict (w_H W) mem) x _ _)).
    split.
    + apply bz_str_bytes; [exact HS | exact Hx | unfold e in *; lia].
    + rewrite length_app. cbn [length].
      replace (x + Z.of_nat (length s + 1)) with (e + 1) by (unfold e, astr_len; lia).
      apply bz_tail_bytes; [exact HT | unfold e, astr_len in *; lia | unfold e in *; lia].
  - rewrite tail_bytes_length. rewrite mod_neg_succ. lia.
Qed.

(* ---- the range check ---- *)

(* the kit's region_in_mem (Bz/A/I_consts.v:20-21) from the contracts' amem_range with eight bytes of band room *)
Lemma region_of_amem : forall p n m, 0 <= p -> 0 <= m -> 0 <= n <= m + 1 -> amem_range p (m + 8) ->
  BK.region_in_mem p n.
Proof.
  intros p n m Hp Hm Hn Ham. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham.
  unfold BK.region_in_mem, BR.kLowMemEnd, BR.kHighShadowEnd, BR.kHighMemEnd.
  destruct Ham as [H|[H1 H2]]; [left | right]; lia.
Qed.

(* the interceptors' range check over a prefix [x, x + n') of a range whose shadow the contract states *)
Lemma chk_of_shadow : forall (W : world tfibsegs) mem x n n' m,
  0 <= x -> x + n <= 2 ^ 63 -> 0 <= n < 2 ^ 32 ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n ->
  (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n) ->
  amem_range x (m + 8) -> 0 <= m -> 0 <= n' <= n -> n' <= m + 1 ->
  BQ.chk_ok (mrestrict (w_H W) mem) x n'.
Proof.
  intros W mem x n n' m Hx Hxn Hn HRA HV Ham Hm Hn' Hnm.
  pose proof Ham as Ham'. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham'.
  destruct (Z.eq_dec n' 0) as [->|Hn0].
  - split; [intros i Hi; lia|]. split; [intros Hq; lia | intros Hq; lia].
  - split; [|split].
    + apply (RtBzStr.acc_of_range_addressable (w_H W) mem x n' ltac:(lia) ltac:(lia) ltac:(lia)).
      intros y Hy. apply HRA. lia.
    + apply (RtBzStr.qc_words_of_hull (w_H W) mem x n' ltac:(lia) ltac:(lia) ltac:(lia)).
      apply RtBzStr.hull_of_shadow_hull_vis.
      intros s Hs. apply (HV ltac:(lia)). unfold shadow_addr in *.
      assert ((x + n' - 1) / 8 <= (x + n - 1) / 8) by (apply Z.div_le_mono; lia).
      assert ((SHADOW_OFF + (x + n' - 1) / 8) / 8 <= (SHADOW_OFF + (x + n - 1) / 8) / 8)
        by (apply Z.div_le_mono; lia).
      lia.
    + intros _. split; [exact (region_of_amem x n' m Hx Hm ltac:(lia) Ham) | lia].
Qed.

Lemma chk_of_read : forall stk (W : world tfibsegs) regs mem x n n' m,
  aread_ok tfibsegs stk W regs mem x n ->
  amem_range x (m + 8) -> 0 <= m -> 0 <= n' <= n -> n' <= m + 1 ->
  BQ.chk_ok (mrestrict (w_H W) mem) x n'.
Proof.
  intros stk W regs mem x n n' m (Hx & Hxn & Hn & _ & _ & HRA & HV).
  exact (chk_of_shadow W mem x n n' m Hx Hxn Hn HRA HV).
Qed.

Lemma chk_of_write : forall stk ly S (W : world tfibsegs) regs mem d n n' m,
  awrite_ok tfibsegs B stk ly S W regs mem d n ->
  amem_range d (m + 8) -> 0 <= m -> 0 <= n' <= n -> n' <= m + 1 ->
  BQ.chk_ok (mrestrict (w_H W) mem) d n'.
Proof.
  intros stk ly S W regs mem d n n' m (Hd & Hdn & Hn & _ & _ & HRA & HV).
  exact (chk_of_shadow W mem d n n' m Hd Hdn Hn HRA HV).
Qed.

(* ---- separation of a read range from the callee's stack window ---- *)

Lemma sep_of_read : forall stk (W : world tfibsegs) regs mem x n,
  0 < stk -> 0 < n -> aread_ok tfibsegs stk W regs mem x n ->
  x + n <= spZ regs - stk \/ spZ regs <= x.
Proof.
  intros stk W regs mem x n Hstk Hn (Hx & Hxn & _ & HB & _).
  destruct (Z_lt_le_dec x (spZ regs - stk)) as [L|L].
  - left. destruct (Z_lt_le_dec (spZ regs - stk) (x + n)) as [R|R]; [|lia].
    exfalso. destruct (HB (spZ regs - stk) ltac:(lia)) as (_ & Hns).
    apply Hns. unfold ascratch_stk. lia.
  - right. destruct (HB x ltac:(lia)) as (_ & Hns).
    unfold ascratch_stk in Hns. lia.
Qed.

Lemma sep_of_write : forall stk ly S (W : world tfibsegs) regs mem d n,
  0 < stk -> 0 < n -> awrite_ok tfibsegs B stk ly S W regs mem d n ->
  d + n <= spZ regs - stk \/ spZ regs <= d.
Proof.
  intros stk ly S W regs mem d n Hstk Hn (Hd & Hdn & _ & HB & _).
  destruct (Z_lt_le_dec d (spZ regs - stk)) as [L|L].
  - left. destruct (Z_lt_le_dec (spZ regs - stk) (d + n)) as [R|R]; [|lia].
    exfalso. destruct (HB (spZ regs - stk) ltac:(lia)) as (_ & _ & Hns).
    apply Hns. unfold ascratch_stk. lia.
  - right. destruct (HB d ltac:(lia)) as (_ & _ & Hns).
    unfold ascratch_stk in Hns. lia.
Qed.

(* ---- a byte a contract says is writable is a byte of the store, not a hidden one ---- *)

Lemma wH_false_of_writable : forall (W : world tfibsegs) mem a,
  writable_at tfibsegs (mrestrict (w_H W) mem) a -> w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W mem a HW. destruct (w_H W (Z_to_bv 64 a)) eqn:E; [|reflexivity].
  exfalso. apply HW. unfold wview, mrestrict. rewrite E.
  rewrite (w_Hoff W (Z_to_bv 64 a) E). reflexivity.
Qed.

(* ---- eight bytes the contract reads as a word are a cell the walks read ---- *)

Lemma aview_byte_range : forall (W : world tfibsegs) mem a v,
  aview tfibsegs (w_H W) mem a = Some v -> 0 <= v < 256.
Proof.
  intros W mem a v Hv. unfold aview in Hv.
  destruct (mbyte tfibsegs (mrestrict (w_H W) mem) a) as [b|]; [|discriminate].
  cbn [option_map] in Hv. injection Hv as <-.
  pose proof (bv_unsigned_in_range 8 b) as X. unfold bv_modulus in X. cbn in X. lia.
Qed.

Lemma bz_bytes_of_rdword : forall (W : world tfibsegs) mem a v,
  rdword (aview tfibsegs (w_H W) mem) a = Some v -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  BM.bytes_at BI.asegs (mrestrict (w_H W) mem) a (BM.le8 (Z_to_bv 64 v)).
Proof.
  intros W mem a v Hw Ha Hb.
  assert (Hv64 : 0 <= v < 2 ^ 64).
  { pose proof Hw as Hw'. unfold rdword in Hw'.
    destruct (aview tfibsegs (w_H W) mem a) as [b0|] eqn:E0; [|discriminate].
    destruct (aview tfibsegs (w_H W) mem (a + 1)) as [b1|] eqn:E1; [|discriminate].
    destruct (aview tfibsegs (w_H W) mem (a + 2)) as [b2|] eqn:E2; [|discriminate].
    destruct (aview tfibsegs (w_H W) mem (a + 3)) as [b3|] eqn:E3; [|discriminate].
    destruct (aview tfibsegs (w_H W) mem (a + 4)) as [b4|] eqn:E4; [|discriminate].
    destruct (aview tfibsegs (w_H W) mem (a + 5)) as [b5|] eqn:E5; [|discriminate].
    destruct (aview tfibsegs (w_H W) mem (a + 6)) as [b6|] eqn:E6; [|discriminate].
    destruct (aview tfibsegs (w_H W) mem (a + 7)) as [b7|] eqn:E7; [|discriminate].
    injection Hw' as <-.
    pose proof (aview_byte_range W mem _ _ E0).
    pose proof (aview_byte_range W mem _ _ E1).
    pose proof (aview_byte_range W mem _ _ E2).
    pose proof (aview_byte_range W mem _ _ E3).
    pose proof (aview_byte_range W mem _ _ E4).
    pose proof (aview_byte_range W mem _ _ E5).
    pose proof (aview_byte_range W mem _ _ E6).
    pose proof (aview_byte_range W mem _ _ E7). lia. }
  (* the eight bytes of the word, as AE2y reads them off rdword *)
  pose proof (AE2y.val_mem_of_rdword (w_H W) mem a v Hw) as HV.
  split; [exact Ha|]. split; [rewrite BM.length_le8; cbn; lia|].
  intros i Hi. rewrite BM.length_le8 in Hi.
  rewrite (RtBzPre.le8_nth v i Hv64 Hi), RtBzPre.mrd_mbyte. exact (HV i Hi).
Qed.

(* the stack-protector pair of the musl bodies, as the walks read it *)
Lemma bz_guard_bytes : forall (W : world tfibsegs) mem gotw guard,
  aguard_ok tfibsegs W mem gotw guard -> 0 <= gotw -> gotw + 8 <= 2 ^ 64 ->
  0 <= guard -> guard + 8 <= 2 ^ 64 ->
  BM.bytes_at BI.asegs (mrestrict (w_H W) mem) gotw (BM.le8 (Z_to_bv 64 guard)) /\
  exists can, BM.bytes_at BI.asegs (mrestrict (w_H W) mem) guard (BM.le8 can).
Proof.
  intros W mem gotw guard (HG & can & HC) H1 H2 H3 H4.
  split; [exact (bz_bytes_of_rdword W mem gotw guard HG H1 H2)|].
  exists (Z_to_bv 64 can). exact (bz_bytes_of_rdword W mem guard can HC H3 H4).
Qed.

End a.
