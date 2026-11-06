(* lv2_locate_manifest_readings: the C8 segment, from 0x81f20 (after strchr (ns, '>')) to the next cut
   (lv2_locate.c:131-135, plain_local :44-46; readings_names.dis lines 209-250 and 274-277).
   r = 0 -> 0x820b0 (s5 = 0) -> the shared return; r <> 0 (r = ns + o): o >= uri_len -> RD_CONT -> L;
   strncmp (uri, ns, o) <> 0 -> RD_CONT -> L; local = uri + o, n = strlen (local) (n = 0 is dead), local[n - 1] = '.'
   -> RD_CONT -> L; else -> plain_local's loop head 0x81fc8 at q = 0.
   Three symbolic states, each built from a Prop at its pc: A at 0x81f20 (rd_C8), B at 0x81f4c after strncmp (rd_c9),
   C at 0x81f70 after strlen (rd_c10). Address arithmetic the walk needs as one atom is declared as f_alias entries
   whose left sides are the executor's own linear forms (probed). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YCbm.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI00 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_g3kit FMW_rd_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_rd_cuts FMW_rd_ret ACej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- pure facts (fm's model, ManifestModel; the step lemmas of lib/Prog/readings_scan.v:189-274 restated) ---- *)
Lemma c8_find_first : forall (l : list Z) c j, FMH_Rt.first_at l c j -> find_idx (fun x => x =? c) l = Some j.
Proof.
induction l as [|x l IH]; intros c j (Hj & Hn & Hni); cbn [length] in Hj; [lia|].
destruct j as [|j]; cbn [nth firstn In find_idx] in Hn, Hni |- *.
- subst x. rewrite Z.eqb_refl. reflexivity.
- destruct (Z.eqb_spec x c) as [->|Hx]; [exfalso; apply Hni; left; reflexivity|].
  rewrite (IH c j); [reflexivity|]. split; [lia|]. split; [exact Hn|]. intros Hin. apply Hni. right. exact Hin.
Qed.

Lemma c8_find_none : forall (l : list Z) c, ~ In c l -> find_idx (fun x => x =? c) l = None.
Proof.
induction l as [|x l IH]; intros c H; cbn [find_idx]; [reflexivity|].
destruct (Z.eqb_spec x c) as [->|Hx]; [exfalso; apply H; left; reflexivity|].
rewrite IH; [reflexivity|]. intros Hin. apply H. right. exact Hin.
Qed.

Lemma c8_find_lt : forall f (l : list Z) o, find_idx f l = Some o -> (o < length l)%nat.
Proof.
intros f l. induction l as [|x l IH]; intros o H; cbn in H; [discriminate|].
destruct (f x); [inversion H; cbn; lia|].
destruct (find_idx f l) as [o'|] eqn:E; cbn in H; [|discriminate]. inversion H; subst. cbn. specialize (IH o' eq_refl). lia.
Qed.

Lemma c8_nth_skipn : forall (l : list Z) k j, nth j (skipn k l) 0 = nth (k + j) l 0.
Proof. induction l as [|x l IH]; intros [|k] j; cbn; try reflexivity; [destruct j; reflexivity | apply IH]. Qed.

Lemma c8_last_nth : forall (l : list Z) d, l <> [] -> last l d = nth (pred (length l)) l d.
Proof.
induction l as [|x l IH]; intros d H; [congruence|]. destruct l as [|y l']; [reflexivity|].
change (last (x :: y :: l') d) with (last (y :: l') d). rewrite IH by discriminate. reflexivity.
Qed.

Lemma c8_last_skipn : forall (l : list Z) o, (o < length l)%nat -> last (skipn o l) 0 = nth (pred (length l)) l 0.
Proof.
intros l o Ho. rewrite c8_last_nth.
- rewrite length_skipn, c8_nth_skipn. f_equal. lia.
- intros H. apply (f_equal (@length Z)) in H. rewrite length_skipn in H. cbn in H. lia.
Qed.

Lemma c8_strn : forall o (l1 l2 : list Z), (o <= length l1)%nat -> (o <= length l2)%nat ->
  FMH_Rt.strn_eq o l1 l2 <-> firstn o l1 = firstn o l2.
Proof.
intros o l1 l2 H1 H2. unfold FMH_Rt.strn_eq. rewrite !firstn_app.
replace (o - length l1)%nat with 0%nat by lia. replace (o - length l2)%nat with 0%nat by lia.
cbn [firstn]. rewrite !app_nil_r. tauto.
Qed.

Lemma c8_decl : forall cx i s11 p1 p2 p3, rd_decl cx i s11 p1 p2 p3 ->
  decl (cx_tb cx) i = match find_idx (fun c => c =? 62) (skipn (S p3) (cx_tb cx)) with
                      | None => DCut
                      | Some o => DFound p1 (p2 - p1) (S p3) o (S p3 + o)
                      end.
Proof.
intros cx i s11 p1 p2 p3 (Hh & _ & Hs & E1 & E2 & Hc & E3 & Hl & _).
unfold decl. rewrite Hh. cbv beta iota. rewrite Hs. cbn [negb]. cbv beta iota zeta.
rewrite <- E1, <- E2, Hc, Z.eqb_refl. cbn [negb]. cbv beta iota zeta.
rewrite <- E3, Hl, Z.eqb_refl. reflexivity.
Qed.

Lemma c8_acc_next : forall cx i d f name nl ns nl2 close,
  rd_acc cx i d (S f) -> (i < length (cx_tb cx))%nat ->
  decl (cx_tb cx) i = DFound name nl ns nl2 close -> matches (cx_tb cx) (cx_ub cx) ns nl2 = false ->
  (S close <= length (cx_tb cx))%nat -> (i < S close)%nat ->
  rd_acc cx (S close) d f.
Proof.
intros cx i d f name nl ns nl2 close (H1 & H2 & H3 & H4) Hi Hd Hm Hc Hic.
assert (Hs : scan (cx_tb cx) (cx_ub cx) i d (S f) = scan (cx_tb cx) (cx_ub cx) (S close) d f).
{ cbn [scan]. rewrite (proj2 (Nat.leb_gt _ _) Hi), Hd, Hm. reflexivity. }
assert (Hr : readings (cx_tb cx) (cx_ub cx) i d (S f) = readings (cx_tb cx) (cx_ub cx) (S close) d f).
{ cbn [readings]. rewrite (proj2 (Nat.leb_gt _ _) Hi), Hd, Hm. reflexivity. }
split; [lia|]. split; [lia|]. split; [rewrite H3; exact Hs|]. rewrite H4, Hr. reflexivity.
Qed.

Lemma c8_acc_cut : forall cx i d f, rd_acc cx i d (S f) -> (i < length (cx_tb cx))%nat ->
  decl (cx_tb cx) i = DCut ->
  names (cx_tb cx) (cx_ub cx) = 0 /\ nreadings (cx_tb cx) (cx_ub cx) = d.
Proof.
intros cx i d f (_ & _ & H3 & H4) Hi Hd. cbn [scan readings] in H3, H4.
rewrite (proj2 (Nat.leb_gt _ _) Hi), Hd in H3, H4. split; [exact H3 | lia].
Qed.

Lemma c8_nm_len : forall tb ub ns o, (length ub <= o)%nat -> matches tb ub ns o = false.
Proof. intros tb ub ns o H. unfold matches. rewrite (proj2 (Nat.ltb_ge _ _) H). reflexivity. Qed.

Lemma c8_nm_neq : forall tb ub ns o, firstn o (skipn ns tb) <> firstn o ub -> matches tb ub ns o = false.
Proof.
intros tb ub ns o H. unfold matches. destruct (o <? length ub)%nat; cbn [andb]; [|reflexivity].
destruct (zl_eqb (firstn o (skipn ns tb)) (firstn o ub)) eqn:Hz; [|reflexivity].
apply zl_eqb_eq in Hz. contradiction.
Qed.

Lemma c8_nm_dot : forall tb ub ns o, last (skipn o ub) 0 = 46 -> matches tb ub ns o = false.
Proof.
intros tb ub ns o H. unfold matches.
assert (Hp : plain_name (skipn o ub) = false).
{ unfold plain_name. destruct (skipn o ub) as [|x l] eqn:Hs; [reflexivity|]. rewrite H. reflexivity. }
rewrite Hp, andb_false_r. reflexivity.
Qed.

(* ---- a C string's suffix is a C string ---- *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma c8_cstr_ok_skipn : forall W mem p (l : list Z) k, cstr_ok tfibsegs W mem p l -> (k <= length l)%nat ->
  cstr_ok tfibsegs W mem (p + Z.of_nat k) (skipn k l).
Proof.
intros W mem p l k ((Hg & Hnz) & H4 & Hc & H32 & Ham & Hra & Hhv & Htl) Hk.
pose proof asan_consts as (C1 & _).
unfold cstr_ok, cstr. rewrite length_skipn.
assert (Lk : Z.of_nat (length l - k) = Z.of_nat (length l) - Z.of_nat k) by lia.
split; [split|].
- intros j Hj. rewrite length_app, length_skipn in Hj. cbn [length] in Hj.
  destruct (Hg (k + j)%nat ltac:(rewrite length_app; cbn [length]; lia)) as [Hv Hr].
  assert (Hn : nth j (skipn k l ++ [0]) 0 = nth (k + j) (l ++ [0]) 0).
  { rewrite <- c8_nth_skipn, skipn_app. replace (k - length l)%nat with 0%nat by lia. reflexivity. }
  rewrite Hn. replace (p + Z.of_nat k + Z.of_nat j) with (p + Z.of_nat (k + j)) by lia. split; assumption.
- rewrite <- (firstn_skipn k l) in Hnz. apply Forall_app in Hnz. exact (proj2 Hnz).
- rewrite Lk. split; [lia|]. split; [lia|]. split; [lia|]. split.
  { unfold amem_range in *. lia. }
  split.
  { eapply range_addressable_sub; [exact Hra | lia | lia]. }
  split.
  { unfold shadow_hull_vis in *. intros s Hs. apply Hhv.
    replace (p + Z.of_nat k + (Z.of_nat (length l) - Z.of_nat k + 1) - 1)
      with (p + (Z.of_nat (length l) + 1) - 1) in Hs by lia.
    split; [|lia].
    assert (shadow_addr p <= shadow_addr (p + Z.of_nat k)).
    { unfold shadow_addr. pose proof (Z.div_le_mono p (p + Z.of_nat k) 8 ltac:(lia) ltac:(lia)). lia. }
    pose proof (Z.div_le_mono (shadow_addr p) (shadow_addr (p + Z.of_nat k)) 8 ltac:(lia) ltac:(lia)). lia. }
  intros a Ha. apply Htl.
  replace (p + Z.of_nat k + (Z.of_nat (length l) - Z.of_nat k)) with (p + Z.of_nat (length l)) in Ha by lia.
  exact Ha.
Qed.
End s.

(* ---- arithmetic on words ---- *)
Lemma c8_u64 : forall z, bv_unsigned (w64 z) = z mod 2 ^ 64.
Proof. intros z. unfold w64. rewrite Z_to_bv_unsigned. reflexivity. Qed.
Lemma c8_u64s : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof. intros z Hz. rewrite c8_u64. apply Z.mod_small. exact Hz. Qed.

Ltac c8_clear_props := repeat match goal with H : ?T |- _ => lazymatch type of T with Prop => clear H end end.
(* sv_denot E lhs = sv_denot E (SOff k 0) for a linear lhs: its linear normal form (YP0e.v lin_nf_sound) *)
Ltac c8_ulin :=
  lazymatch goal with |- U ?E ?v = _ =>
    let r := eval vm_compute in (lin_nf v) in
    lazymatch r with Some (?l, ?c) =>
      rewrite (lin_nf_sound E v l c ltac:(vm_compute; reflexivity)); cbn [lin_denot] end end.
Ltac c8_alias := apply U_inj; c8_ulin; rewrite U_SOff.
Ltac c8_zmod := unfold zcanon, M64, rd_p0, rd_s10 in *; c8_clear_props; Z.div_mod_to_equations; lia.

(* ---- memory kept across the segment: everything outside the runtime call's window below F and slot 0x38 ---- *)
Definition rd_win (cx : rdcx) (a : Z) : Prop :=
  cx_F cx - STK_RT_STR <= a < cx_F cx \/ cx_F cx + 0x38 <= a < cx_F cx + 0x40.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Definition rd_kept (cx : rdcx) (W : world tfibsegs) (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ rd_win cx a -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a.

Lemma c8_kept_refl : forall cx W m, rd_kept cx W m m.
Proof. intros cx W m a _ _. reflexivity. Qed.

Lemma c8_nowin : forall E rs, forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> forall a, ~ in_wrange E rs a.
Proof.
intros E rs H a (r & Hin & Hr). rewrite forallb_forall in H. specialize (H r Hin). apply Z.leb_le in H. lia.
Qed.

Lemma c8_frame_kept : forall cx E rs (W : world tfibsegs) m0 m1 m, frame_of E rs (mrestrict (w_H W) m0) (mrestrict (w_H W) m1) ->
  (forall a, in_wrange E rs a -> rd_win cx a) -> rd_kept cx W m m0 -> rd_kept cx W m m1.
Proof.
intros cx E rs W m0 m1 m HF Hw HK a Ha Hn.
rewrite (g3_aview_frame E rs (w_H W) m0 m1 HF a Ha); [exact (HK a Ha Hn)|].
intros Hin. apply Hn. apply Hw. exact Hin.
Qed.

Lemma c8_frame_eq : forall E rs (W : world tfibsegs) m0 m1 m, frame_of E rs (mrestrict (w_H W) m0) (mrestrict (w_H W) m1) ->
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
  (forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) m0 a = aview tfibsegs (w_H W) m a) ->
  forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) m1 a = aview tfibsegs (w_H W) m a.
Proof.
intros E rs W m0 m1 m HF Hw HK a Ha.
rewrite (g3_aview_frame E rs (w_H W) m0 m1 HF a Ha); [exact (HK a Ha)|]. exact (c8_nowin E rs Hw a).
Qed.

Lemma c8_kept_of_eq : forall cx (W : world tfibsegs) m m', (forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  rd_kept cx W m m'.
Proof. intros cx W m m' H a Ha _. exact (H a Ha). Qed.

Lemma c8_call_kept : forall cx W m m0 m1, rd_kept cx W m m0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (cx_F cx - STK_RT_STR <= a < cx_F cx) ->
     aview tfibsegs (w_H W) m1 a = aview tfibsegs (w_H W) m0 a) ->
  rd_kept cx W m m1.
Proof.
intros cx W m m0 m1 HK Hc a Ha Hn. rewrite (Hc a Ha); [exact (HK a Ha Hn)|]. intros Hw. apply Hn. left. exact Hw.
Qed.

Lemma c8_bounds : forall CTX cx, rd_base B CTX cx ->
  alloc_ceiling + STK_readings <= cx_sp cx /\ cx_sp cx + 16 <= 2 ^ 47 /\ cx_sp cx mod 16 = 0.
Proof.
intros CTX cx (HAN & _ & _ & _ & _ & _ & _ & Htopr & _).
pose proof HAN as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold cx_sp in *. lia.
Qed.

Lemma c8_val_kept : forall cx W m m' a n v, rd_kept cx W m m' -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat n -> ~ rd_win cx x) ->
  val_mem tfibsegs (rdW W m) a n v -> val_mem tfibsegs (rdW W m') a n v.
Proof.
intros cx W m m' a n v HK H0 H1 Hw Hv. apply (g3_val_mem_kept W W m m'); [exact Hv|].
intros i Hi. apply HK; [lia|]. apply Hw. lia.
Qed.

Lemma c8_slots_kept : forall CTX cx W m m' sl, rd_base B CTX cx -> rd_kept cx W m m' ->
  Forall (fun s => (0 <= fst s /\ fst s + 8 <= 0x38) \/ (0x40 <= fst s <= 0x100)) sl ->
  rd_slots_ok cx W m sl -> rd_slots_ok cx W m' sl.
Proof.
intros CTX cx W m m' sl HB HK Hs H. pose proof (c8_bounds CTX cx HB) as (Bs1 & Bs2 & _).
pose proof asan_consts as (C1 & _). assert (STK_readings = 16624) by reflexivity.
assert (STK_RT_STR = 8192) by reflexivity.
unfold rd_slots_ok in *. rewrite Forall_forall in Hs, H |- *. intros s Hin.
destruct (H s Hin) as [Hv Hr]. split; [|exact Hr]. specialize (Hs s Hin).
assert (HF : cx_F cx = cx_sp cx - 208) by reflexivity.
apply (c8_val_kept cx W m m' _ 8 _ HK); [lia | lia | | exact Hv].
intros x Hx Hw. unfold rd_win in Hw. cbn [Z.of_nat Pos.of_succ_nat] in Hx. lia.
Qed.

Lemma c8_slots_eq : forall cx (W : world tfibsegs) m m' sl,
  (forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  Forall (fun s => 0 <= cx_F cx + fst s /\ cx_F cx + fst s + 8 <= 2 ^ 64) sl ->
  rd_slots_ok cx W m sl -> rd_slots_ok cx W m' sl.
Proof.
intros cx W m m' sl HE Hs H. unfold rd_slots_ok in *. rewrite Forall_forall in Hs, H |- *. intros s Hin.
destruct (H s Hin) as [Hv Hr]. split; [|exact Hr]. specialize (Hs s Hin).
apply (g3_val_mem_kept W W m m'); [exact Hv|]. intros i Hi. apply HE. cbn in Hi. lia.
Qed.

(* rd_loop carries over a run or a runtime call that writes inside rd_win only *)
Lemma c8_loop_kept : forall CTX cx d ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
  rd_base B CTX cx -> rd_loop B cx d ly3 S3 W3 regs3 mem3 md3 ->
  ajournal tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx)
    (cx_md cx) [] ly3 S3 W3 mem4 md4 EV_names ->
  rd_kept cx W3 mem3 mem4 ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 8 = getr regs3 8 -> getr regs4 9 = getr regs3 9 -> getr regs4 18 = getr regs3 18 ->
  rd_loop B cx d ly3 S3 W3 regs4 mem4 md4.
Proof.
intros CTX cx d ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HB HL HJ4 HK Q2 Q3 Q4 Q8 Q9 Q18.
pose proof (c8_bounds CTX cx HB) as (Bs1 & Bs2 & _).
pose proof asan_consts as (C1 & _). assert (STK_readings = 16624) by reflexivity.
assert (STK_RT_STR = 8192) by reflexivity.
assert (HF : cx_F cx = cx_sp cx - 208) by reflexivity.
assert (HKL : g3_low_kept W3 W3 mem3 mem4).
{ intros a Ha. apply HK; [lia|]. unfold rd_win. lia. }
destruct HL as ((HJ & Hk & R2 & R3 & R4 & R8 & HSV & K16 & HRO & Ct & Cu & Kt & Ku) & R9 & R18 & HSL & HVrp & HPm & HGl
  & Hrest).
split; [|split; [|split; [|split; [|split; [|split; [|split; [|exact Hrest]]]]]]].
- split; [exact HJ4|]. split; [exact Hk|].
  split; [rewrite Q2; exact R2|]. split; [rewrite Q3; exact R3|]. split; [rewrite Q4; exact R4|].
  split; [rewrite Q8; exact R8|].
  split.
  { unfold rd_saved_ok in *. rewrite Forall_forall in HSV |- *. intros s Hin.
    assert (Hs : 104 <= fst s <= 200).
    { cbv [RD_SAVED In] in Hin. repeat (destruct Hin as [<-|Hin]; [cbn; lia|]). destruct Hin. }
    apply (c8_val_kept cx W3 mem3 mem4 _ 8 _ HK); [lia | lia | | exact (HSV s Hin)].
    intros x Hx Hw. unfold rd_win in Hw. cbn in Hx. lia. }
  split.
  { intros a Ha. rewrite (HK a); [exact (K16 a Ha) | lia |]. unfold rd_win. lia. }
  split; [exact (g3_arodata_kept B W3 W3 mem3 mem4 HRO HKL)|].
  split; [exact (g3_cstr_ok_kept W3 W3 mem3 mem4 _ _ Ct HKL)|].
  split; [exact (g3_cstr_ok_kept W3 W3 mem3 mem4 _ _ Cu HKL)|].
  split; [exact Kt | exact Ku].
- rewrite Q9. exact R9.
- rewrite Q18. exact R18.
- apply (c8_slots_kept CTX cx W3 mem3 mem4 _ HB HK); [|exact HSL].
  unfold rd_loc_list. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia.
- apply (c8_val_kept cx W3 mem3 mem4 _ 8 _ HK); [lia | lia | | exact HVrp].
  intros x Hx Hw. unfold rd_win in Hw. cbn in Hx. lia.
- exact HPm.
- exact (g3_fm_glob_kept W3 W3 mem3 mem4 _ _ _ _ HGl HKL).
Qed.

(* the cut after strncmp (0x81f4c): a0 = v, strncmp's answer; s3 = ns_end *)
Definition rd_c9 (cx : rdcx) (i d f s11 p1 p2 p3 o : nat) (v : Z) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  let p0 := rd_p0 cx i s11 in let s10 := rd_s10 i s11 p3 in
  rd_loop B cx d ly3 S3 W3 regs3 mem3 md3 /\ rd_acc cx i d f /\ (i < length (cx_tb cx))%nat /\
  rd_decl cx i s11 p1 p2 p3 /\
  find_idx (fun c => c =? 62) (skipn (S p3) (cx_tb cx)) = Some o /\ (o < length (cx_ub cx))%nat /\
  rd_slots_ok cx W3 mem3 [(0x10, (- p0) mod 2 ^ 64)] /\
  getr regs3 19 = w64 (cx_t cx + Z.of_nat (S p3) + Z.of_nat o) /\ getr regs3 20 = w64 (cx_u cx - 3 - p0 - s10) /\
  getr regs3 21 = w64 (cx_u cx - 2 - Z.of_nat s11 - (cx_t cx + Z.of_nat i) - s10) /\
  getr regs3 22 = w64 (cx_t cx + Z.of_nat p1) /\ getr regs3 23 = w64 (Z.of_nat p2 - Z.of_nat p1) /\
  getr regs3 24 = w64 (cx_t cx + Z.of_nat i) /\ getr regs3 25 = w64 (cx_u cx - 2 - p0 - s10) /\
  getr regs3 26 = w64 s10 /\ getr regs3 27 = w64 (Z.of_nat s11) /\
  getr regs3 10 = w64 v /\ 0 <= v < 2 ^ 64 /\ (v = 0 <-> FMH_Rt.strn_eq o (cx_ub cx) (skipn (S p3) (cx_tb cx))).

(* the cut after strlen (0x81f70): the namespace matched the uri's first o bytes; local = uri + o in slot 0x38;
   a0 = n = uri_len - o *)
Definition rd_c10 (cx : rdcx) (i d f s11 p1 p2 p3 o : nat) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  let p0 := rd_p0 cx i s11 in let s10 := rd_s10 i s11 p3 in
  rd_loop B cx d ly3 S3 W3 regs3 mem3 md3 /\ rd_acc cx i d f /\ (i < length (cx_tb cx))%nat /\
  rd_decl cx i s11 p1 p2 p3 /\
  find_idx (fun c => c =? 62) (skipn (S p3) (cx_tb cx)) = Some o /\ (o < length (cx_ub cx))%nat /\
  firstn o (skipn (S p3) (cx_tb cx)) = firstn o (cx_ub cx) /\
  rd_slots_ok cx W3 mem3 [(0x38, cx_u cx + Z.of_nat o)] /\
  getr regs3 19 = w64 (cx_t cx + Z.of_nat (S p3) + Z.of_nat o) /\ getr regs3 20 = w64 (cx_u cx - 3 - p0 - s10) /\
  getr regs3 21 = w64 (cx_u cx - 2 - Z.of_nat s11 - (cx_t cx + Z.of_nat i) - s10) /\
  getr regs3 22 = w64 (cx_t cx + Z.of_nat p1) /\ getr regs3 23 = w64 (Z.of_nat p2 - Z.of_nat p1) /\
  getr regs3 24 = w64 (cx_t cx + Z.of_nat i) /\ getr regs3 25 = w64 (cx_u cx - 2 - p0 - s10) /\
  getr regs3 26 = w64 s10 /\ getr regs3 27 = w64 (Z.of_nat s11) /\
  getr regs3 10 = w64 (Z.of_nat (length (cx_ub cx) - o)).
End k.

(* ---- the symbolic states (frame slots at atom 2 = F; s0 = atom 8, the shadow base) ---- *)
Definition C8_Bx : sv := SOff 8 0.
Definition C8_Bspan : Z * Z := (0x7fff8000, 0x7fff8000 + 2 ^ 44 - 1).
Definition C8_M1 : Z := 18446744073709551615.
Definition c8_atoms : list (nat * afact) := [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF 0x7fff8000 0x7fff8000 0)].

(* A, 0x81f20: 32 = uri (0x20), 33 = ns (0x28), 34 = uri_len (0x30), 35 = p0 (0x38), 36 = ns_len o = r - p0 - s10 - 2 *)
Definition c8_alA : list (sv * sv) :=
  [(SAlu ALU_ADD (SAlu ALU_ADD (SOff 10 (-2)) (SMd M_MUL (SOff 26 0) (SLit C8_M1))) (SMd M_MUL (SOff 35 0) (SLit C8_M1)),
    SOff 36 0)].
Definition ss_c8A : sstate :=
  mkSS RD_C8 sr_atoms
    [YP09.mkRegion (Some 2%nat) 0x20 0x40 0x20 0x20 (rd_slot_chunks [(0x20, 0%nat); (0x28, 1%nat); (0x30, 2%nat); (0x38, 3%nat)])]
    None (mkFacts c8_atoms [] c8_alA).

(* B, 0x81f4c: 32 = -p0 (0x10), 33 = uri (0x20), 34 = local = uri + o; slot 0x38 writable *)
Definition c8_alB : list (sv * sv) :=
  [(SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SOff 19 (-2)) (SMd M_MUL (SOff 26 0) (SLit C8_M1))) (SOff 32 0)) (SOff 33 0),
    SOff 34 0)].
Definition ss_c8B : sstate :=
  mkSS RD_C9 sr_atoms
    [YP09.mkRegion (Some 2%nat) 0x10 0x40 0x38 0x40 (rd_slot_chunks [(0x10, 0%nat); (0x20, 1%nat)])]
    None (mkFacts c8_atoms [] c8_alB).

(* C, 0x81f70: 32 = rp (0), 33 = d (8), 34 = uri (0x20), 35 = local + n - 1, 36 = its byte, 37 = local *)
Definition c8_atomsC : list (nat * afact) :=
  c8_atoms ++ [(35%nat, mkAF 0 (2 ^ 47 - 1) 0); (36%nat, mkAF 0 255 0)].
Definition c8_alC : list (sv * sv) :=
  [(SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SOff 10 (-3)) (SOff 19 0))
      (SMd M_MUL (SOff 24 0) (SLit C8_M1))) (SMd M_MUL (SOff 26 0) (SLit C8_M1))) (SMd M_MUL (SOff 27 0) (SLit C8_M1)))
      (SOff 34 0), SOff 35 0);
   (SAlu ALU_ADD (SAlu ALU_ADD (SOff 10 0) (SOff 19 0)) (SOff 20 0), SOff 35 0);
   (SAlu ALU_ADD (SOff 19 0) (SOff 25 0), SOff 37 0);
   (SAlu ALU_ADD (SOff 19 0) (SOff 21 0), SOff 37 0)].
Definition ss_c8C : sstate :=
  mkSS RD_C10 sr_atoms
    [YP09.mkRegion (Some 2%nat) 0 0x28 0 0 (rd_slot_chunks [(0, 0%nat); (8, 1%nat); (0x20, 2%nat)]);
     YP09.mkRegion (Some 35%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 36 0))]]
    None (mkFacts c8_atomsC [] c8_alC).

(* ---- tactics over the walk's states ---- *)
(* the machine state of HS as mkst, the pc a literal *)
Ltac c8_mk HS := rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl); cbn [ss_pc].
(* getr at a register the state keeps as its entry atom: the entry register *)
Ltac c8_greg HS EE :=
  lazymatch goal with |- getr _ ?r = getr _ ?r =>
    let Q := fresh "Q" in rreg HS r Q; rewrite Q; apply EE; reflexivity end.
(* the frame of a run with no write window: aview unchanged everywhere *)
Ltac c8_av :=
  lazymatch goal with HFr : frame_of _ ?rs (mrestrict ?H ?m0) (mrestrict _ ?m1) |- _ =>
    lazymatch goal with AV : forall a, _ -> aview _ _ m0 a = aview _ _ ?mem0 a |- _ =>
      let AV2 := fresh "AV" in
      pose proof (c8_frame_eq _ rs _ m0 m1 mem0 HFr ltac:(vm_compute; reflexivity) AV) as AV2;
      clear AV; rename AV2 into AV end end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* the same over rd_kept (runs with no write window) *)
Ltac c8_avk :=
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict ?H ?m0) (mrestrict _ ?m1) |- _ =>
    lazymatch goal with AV : rd_kept ?cx ?W ?mem0 m0 |- _ =>
      let AV2 := fresh "AV" in
      pose proof (c8_frame_kept cx Ex rs W m0 m1 mem0 HFr
        (fun a Ha => False_ind _ (c8_nowin Ex rs ltac:(vm_compute; reflexivity) a Ha)) AV) as AV2;
      clear AV; rename AV2 into AV end end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* the same for B's run, whose window is slot 0x38 *)
Ltac c8_avw U2 :=
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict ?H ?m0) (mrestrict _ ?m1) |- _ =>
    lazymatch goal with AV : rd_kept ?cx ?W ?mem0 m0 |- _ =>
      let AV2 := fresh "AV" in
      assert (AV2 : rd_kept cx W mem0 m1);
      [ apply (c8_frame_kept cx Ex rs W m0 m1 mem0 HFr); [|exact AV];
        let a := fresh "a" in let rg := fresh "rg" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
        intros a (rg & Hin & Hr); vm_compute in Hin; destruct Hin as [<-|[]];
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite U2 in Hr; unfold rd_win; right; lia
      | clear AV; rename AV2 into AV ] end end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* awr_ok for B's slot window (the frame at atom 2 = F = journal sp0 - 224) *)
Ltac c8_awr U2 :=
  lazymatch goal with |- awr_ok ?sg ?BB ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg BB E rs' stk sp0 fp b0 bc ly own) end;
  repeat first
    [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn; lia|]
    | eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -224);
      [reflexivity | rewrite U2; unfold cx_F; lia | cbn; lia | cbn; lia |] ].
(* a register the call keeps (callee-saved) and the state before it holds as an atom *)
Ltac c8_cs HP HS :=
  lazymatch goal with |- getr _ ?r = _ =>
    rewrite (g3_aregs_keep _ _ HP r ltac:(cbv [G3_KEPT In]; repeat (first [left; reflexivity | right])));
    let Q := fresh "Q" in rreg HS r Q; rewrite Q end.
Ltac c8_rr HS := lazymatch goal with |- getr _ ?r = _ => let Q := fresh "Q" in rreg HS r Q; rewrite Q end.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable CTX : list (list Z).
Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis STRNCMP : astrncmp_realizes tfibsegs B PC_strncmp.
Hypothesis STRLEN : astrlen_realizes tfibsegs B PC_strlen.

(* ---- C, 0x81f70: n = strlen (local); local[n - 1] = '.' -> L; else -> plain_local at q = 0 ---- *)
Lemma c8_segC : forall f, rd_seg_L B CTX f -> (forall m, rd_seg_PL B CTX (S f) m) ->
  forall cx i d s11 p1 p2 p3 o ly3 S3 W3 regs3 mem3 md3,
  rd_base B CTX cx -> rd_c10 B cx i d (S f) s11 p1 p2 p3 o ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs RD_C10 regs3 mem3 md3) (rd_post B cx).
Proof.
intros f SL SPL cx i d s11 p1 p2 p3 o ly3 S3 W3 regs3 mem3 md3 HB HC.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (c8_bounds B CTX cx HB) as (Bs1 & Bs2 & Bs3).
assert (FFR : STK_readings = 16624) by reflexivity. assert (FRT : STK_RT_STR = 8192) by reflexivity.
assert (HF : cx_F cx = cx_sp cx - 208) by reflexivity.
assert (HFm : cx_F cx mod 16 = 0).
{ rewrite HF. replace (cx_sp cx - 208) with (cx_sp cx + (-13) * 16) by lia. rewrite Z_mod_plus_full. exact Bs3. }
destruct HC as (HL & HA & Hi & HD & Hfo & Hou & Hfe & HS38 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & R10).
pose proof HL as ((HJ & Hk & R2 & R3 & R4 & R8 & _ & _ & HRO & Ct & Cu & _ & _) & R9 & R18 & HSL & _ & _ & _ & Hcf
  & Hub0 & _ & Hd16).
pose proof Ct as (_ & Ht4 & Htc & _).
pose proof Cu as ((HGu & HNZ) & Hu4 & Huc & H32 & Ham & Hra & _).
pose proof HD as (Hh & Hs11 & Hsp & E1 & E2 & Hc58 & E3 & Hc60 & Hp3).
pose proof (c8_find_lt _ _ _ Hfo) as Hol. rewrite length_skipn in Hol.
unfold rd_slots_ok, rd_loc_list in HSL.
apply Forall_cons_iff in HSL as [(V00 & _) HSL]. apply Forall_cons_iff in HSL as [(V08 & _) HSL].
apply Forall_cons_iff in HSL as [_ HSL]. apply Forall_cons_iff in HSL as [(V20 & _) _].
cbn [fst snd] in V00, V08, V20.
destruct (HGu (pred (length (cx_ub cx))) ltac:(rewrite length_app; cbn [length]; lia)) as [Vc Rc].
rewrite app_nth1 in Vc, Rc by lia.
set (c := nth (pred (length (cx_ub cx))) (cx_ub cx) 0) in *.
set (lastA := cx_u cx + Z.of_nat o + Z.of_nat (length (cx_ub cx) - o) - 1).
assert (Hlast : lastA = cx_u cx + Z.of_nat (pred (length (cx_ub cx)))) by (unfold lastA; lia).
set (ex := map w64 [cx_sp cx; Z.of_nat d; cx_u cx; lastA; c; cx_u cx + Z.of_nat o]).
set (E := Ereg regs3 ex).
assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs3 q)
  by (intros n q Hn; apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = w64 (cx_sp cx)) by exact (ew_Ereg_extra regs3 ex 0).
assert (E33 : ew E 33 = w64 (Z.of_nat d)) by exact (ew_Ereg_extra regs3 ex 1).
assert (E34 : ew E 34 = w64 (cx_u cx)) by exact (ew_Ereg_extra regs3 ex 2).
assert (E35 : ew E 35 = w64 lastA) by exact (ew_Ereg_extra regs3 ex 3).
assert (E36 : ew E 36 = w64 c) by exact (ew_Ereg_extra regs3 ex 4).
assert (E37 : ew E 37 = w64 (cx_u cx + Z.of_nat o)) by exact (ew_Ereg_extra regs3 ex 5).
assert (Hs10 : 0 <= rd_s10 i s11 p3) by (unfold rd_s10; lia).
assert (U2 : bv_unsigned (ew E 2) = cx_F cx) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply c8_u64s; lia).
assert (U8 : bv_unsigned (ew E 8) = SHADOW_OFF)
  by (rewrite (EE 8%nat 8%bv eq_refl), R8; apply c8_u64s; unfold SHADOW_OFF; lia).
assert (U10 : bv_unsigned (ew E 10) = Z.of_nat (length (cx_ub cx) - o))
  by (rewrite (EE 10%nat 10%bv eq_refl), R10; apply c8_u64s; lia).
assert (U19 : bv_unsigned (ew E 19) = cx_t cx + Z.of_nat (S p3) + Z.of_nat o)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; apply c8_u64s; lia).
assert (U20 : bv_unsigned (ew E 20) = (cx_u cx - 3 - rd_p0 cx i s11 - rd_s10 i s11 p3) mod 2 ^ 64)
  by (rewrite (EE 20%nat 20%bv eq_refl), R20; apply c8_u64).
assert (U21 : bv_unsigned (ew E 21) = (cx_u cx - 2 - Z.of_nat s11 - (cx_t cx + Z.of_nat i) - rd_s10 i s11 p3) mod 2 ^ 64)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply c8_u64).
assert (U24 : bv_unsigned (ew E 24) = cx_t cx + Z.of_nat i)
  by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply c8_u64s; lia).
assert (U25 : bv_unsigned (ew E 25) = (cx_u cx - 2 - rd_p0 cx i s11 - rd_s10 i s11 p3) mod 2 ^ 64)
  by (rewrite (EE 25%nat 25%bv eq_refl), R25; apply c8_u64).
assert (U26 : bv_unsigned (ew E 26) = rd_s10 i s11 p3)
  by (rewrite (EE 26%nat 26%bv eq_refl), R26; apply c8_u64s; unfold rd_s10 in *; lia).
assert (U27 : bv_unsigned (ew E 27) = Z.of_nat s11)
  by (rewrite (EE 27%nat 27%bv eq_refl), R27; apply c8_u64s; lia).
assert (U34 : bv_unsigned (ew E 34) = cx_u cx) by (rewrite E34; apply c8_u64s; lia).
assert (U35 : bv_unsigned (ew E 35) = lastA) by (rewrite E35; apply c8_u64s; unfold lastA; lia).
assert (U36 : bv_unsigned (ew E 36) = c) by (rewrite E36; apply c8_u64s; lia).
assert (U37 : bv_unsigned (ew E 37) = cx_u cx + Z.of_nat o) by (rewrite E37; apply c8_u64s; lia).
assert (HS : st_ok tfibsegs E ss_c8C (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 RD_C10) mem3 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_c8C. apply entry_st_ok_full; try change (Ereg regs3 ex) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (rd_frame_region_ok E _ (cx_F cx)); [exact U2 | lia | lia | intros q Hq; lia |].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd Nat.add].
      * rewrite E32, c8_u64s by lia. exact V00.
      * rewrite E33, c8_u64s by lia. exact V08.
      * rewrite E34, c8_u64s by lia. exact V20.
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U35. split; [unfold lastA; lia|]. split; [unfold lastA; lia|]. split; [intros q Hq; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E _ lastA 0 1 (SOff 36 0) c).
      * cbn [sv_denot]. rewrite U36, Z.add_0_r. reflexivity.
      * cbn. lia.
      * cbn. lia.
      * rewrite Z.add_0_r, Hlast. exact Vc.
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U35.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold lastA.
    repeat split; try exact I; lia.
  - split; [|split; [exact I|]].
    + cbn [f_atoms atoms_ok c8_atomsC c8_atoms app]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U2, U8, U35, U36. change (2 ^ 4) with 16. rewrite HFm, !Z.pow_0_r, !Z.mod_1_r.
      unfold lastA, SHADOW_OFF. repeat split; lia.
    + cbn [f_alias alias_ok c8_alC]. split; [|split; [|split; [|split; [|exact I]]]].
      * c8_alias. rewrite U10, U19, U24, U26, U27, U34, U35. unfold lastA. c8_zmod.
      * c8_alias. rewrite U10, U19, U20, U35. unfold lastA. c8_zmod.
      * c8_alias. rewrite U19, U25, U37. c8_zmod.
      * c8_alias. rewrite U19, U21, U37. c8_zmod. }
clearbody E.
assert (SHOK : sh_ok tfibsegs C8_Bx [] E
  (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 RD_C10) mem3 (seg_rom tfibsegs))))) by constructor.
assert (AV : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W3) mem3 a)
  by reflexivity.
unfold cfg_at. change (w64 RD_C10) with (Z_to_bv 64 RD_C10).
change (unpoison [] mem3) with mem3 in HJ.
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 RD_C10) mem3 (seg_rom tfibsegs))) in HJ.
srr_branch_tok rd_tbl_ok HS SHOK C8_Bspan.
{ (* n = 0: dead *)
  exfalso. rewrite branch_eq_U, U_SOff, U_SLit, U10 in Hc. apply Z.eqb_eq in Hc. unfold zcanon, M64 in Hc.
  rewrite !Z.mod_small in Hc by lia. lia. }
clear Hc. aj_run_tok rd_tbl_ok HS HJ SHOK C8_Bspan.
{ (* the shadow check of local[n - 1] *)
  cbn [ms_mem mkst]. eapply obl_of_range; [exact Hra | | |].
  - unfold C8_Bx. rewrite U_SOff, U8, Z.add_0_r. unfold zcanon, M64. apply Z.mod_small. unfold SHADOW_OFF. lia.
  - rewrite U_SOff, U35, Z.add_0_r. unfold zcanon, M64. rewrite Z.mod_small by (unfold lastA; lia). unfold lastA. lia.
  - rewrite U_SOff, U35, Z.add_0_r. unfold zcanon, M64. rewrite Z.mod_small by (unfold lastA; lia). unfold lastA. lia. }
{ awr_ok_tac. }
c8_av.
srr_branch_tok rd_tbl_ok HS SHOK C8_Bspan.
- (* local[n - 1] = '.': matches is false, back to L at S close *)
  rewrite branch_eq_U, U_SOff, U_SLit in Hc. cbn [ew ewset Nat.eqb] in Hc. rewrite U36 in Hc.
  apply Z.eqb_eq in Hc. unfold zcanon, M64 in Hc. rewrite !Z.mod_small in Hc by lia. rewrite Z.add_0_r in Hc.
  aj_run_to_tok rd_tbl_ok HS HJ SHOK C8_Bspan RD_L.
  { awr_ok_tac. }
  c8_av. c8_mk HS.
  eapply (SL cx (S (S p3 + o))%nat d ly3 S3 W3 _ _ _ HB).
  split; [|split; [|split]].
  + eapply (c8_loop_kept B CTX cx d ly3 S3 W3 regs3 mem3 md3 _ _ _ HB HL HJ (c8_kept_of_eq cx W3 mem3 _ AV));
      c8_greg HS EE.
  + eapply c8_acc_next; [exact HA | exact Hi | rewrite (c8_decl _ _ _ _ _ _ HD), Hfo; reflexivity | | lia | lia].
    apply c8_nm_dot. rewrite c8_last_skipn by lia. exact Hc.
  + c8_rr HS. reflexivity.
  + c8_rr HS. rewrite U19. unfold w64. f_equal. lia.
- (* plain_local's loop at q = 0 *)
  rewrite branch_eq_U, U_SOff, U_SLit in Hc. cbn [ew ewset Nat.eqb] in Hc. rewrite U36 in Hc.
  apply Z.eqb_neq in Hc. unfold zcanon, M64 in Hc. rewrite !Z.mod_small in Hc by lia. rewrite Z.add_0_r in Hc.
  aj_run_to_tok rd_tbl_ok HS HJ SHOK C8_Bspan 0x81fc8.
  { awr_ok_tac. }
  c8_av. c8_mk HS.
  eapply (SPL (length (cx_ub cx) - o)%nat cx i d s11 p1 p2 p3 o 0%nat ly3 S3 W3 _ _ _ ltac:(lia) HB).
  unfold rd_PL. cbv zeta.
  split; [eapply (c8_loop_kept B CTX cx d ly3 S3 W3 regs3 mem3 md3 _ _ _ HB HL HJ (c8_kept_of_eq cx W3 mem3 _ AV));
    c8_greg HS EE|].
  split; [exact HA|]. split; [exact Hi|]. split; [exact HD|]. split; [exact Hfo|]. split; [exact Hou|].
  split; [exact Hfe|]. split; [rewrite c8_last_skipn by lia; exact Hc|]. split; [lia|].
  split; [reflexivity|].
  split.
  { apply (c8_slots_eq cx W3 mem3 _ _ AV); [|exact HS38].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia. }
  split; [c8_rr HS; rewrite (EE 19%nat 19%bv eq_refl); exact R19|].
  split; [c8_rr HS; rewrite E32; reflexivity|].
  split; [c8_rr HS; rewrite E37; unfold w64; f_equal; lia|].
  split; [c8_rr HS; rewrite (EE 22%nat 22%bv eq_refl); exact R22|].
  split; [c8_rr HS; rewrite (EE 23%nat 23%bv eq_refl); exact R23|].
  split; [c8_rr HS; rewrite E33; reflexivity|].
  split; [c8_rr HS; rewrite E37; unfold w64; f_equal; lia|].
  c8_rr HS. rewrite (EE 10%nat 10%bv eq_refl), R10. unfold w64. f_equal. lia.
Qed.

(* ---- B, 0x81f4c: strncmp (uri, ns, o) answered v; v <> 0 -> L; v = 0 -> local = uri + o, strlen (local) ---- *)
Lemma c8_segB : forall f, rd_seg_L B CTX f -> (forall m, rd_seg_PL B CTX (S f) m) ->
  forall cx i d s11 p1 p2 p3 o v ly3 S3 W3 regs3 mem3 md3,
  rd_base B CTX cx -> rd_c9 B cx i d (S f) s11 p1 p2 p3 o v ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs RD_C9 regs3 mem3 md3) (rd_post B cx).
Proof.
intros f SL SPL cx i d s11 p1 p2 p3 o v ly3 S3 W3 regs3 mem3 md3 HB HC.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (c8_bounds B CTX cx HB) as (Bs1 & Bs2 & Bs3).
assert (FFR : STK_readings = 16624) by reflexivity. assert (FRT : STK_RT_STR = 8192) by reflexivity.
assert (HF : cx_F cx = cx_sp cx - 208) by reflexivity.
assert (HFm : cx_F cx mod 16 = 0).
{ rewrite HF. replace (cx_sp cx - 208) with (cx_sp cx + (-13) * 16) by lia. rewrite Z_mod_plus_full. exact Bs3. }
pose proof HB as (HAN & _).
pose proof HAN as (_ & _ & _ & Hgp & Htp & _).
destruct HC as (HL & HA & Hi & HD & Hfo & Hou & HS10 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & R10
  & Hv & Hvs).
pose proof HL as ((HJ & Hk & R2 & R3 & R4 & R8 & _ & _ & HRO & Ct & Cu & _ & _) & R9 & R18 & HSL & _ & _ & _ & Hcf
  & Hub0 & _ & Hd16).
pose proof Ct as (_ & Ht4 & Htc & _).
pose proof Cu as (_ & Hu4 & Huc & _).
pose proof HD as (Hh & Hs11 & Hsp & E1 & E2 & Hc58 & E3 & Hc60 & Hp3).
pose proof (c8_find_lt _ _ _ Hfo) as Hol. rewrite length_skipn in Hol.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
unfold rd_slots_ok, rd_loc_list in HSL.
apply Forall_cons_iff in HSL as [_ HSL]. apply Forall_cons_iff in HSL as [_ HSL].
apply Forall_cons_iff in HSL as [_ HSL]. apply Forall_cons_iff in HSL as [(V20 & _) _].
cbn [fst snd] in V20.
pose proof HS10 as HS10'. unfold rd_slots_ok in HS10'. apply Forall_cons_iff in HS10' as [(V10 & _) _].
cbn [fst snd] in V10.
set (ex := map w64 [(- rd_p0 cx i s11) mod 2 ^ 64; cx_u cx; cx_u cx + Z.of_nat o]).
set (E := Ereg regs3 ex).
assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs3 q)
  by (intros n q Hn; apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = w64 ((- rd_p0 cx i s11) mod 2 ^ 64)) by exact (ew_Ereg_extra regs3 ex 0).
assert (E33 : ew E 33 = w64 (cx_u cx)) by exact (ew_Ereg_extra regs3 ex 1).
assert (E34 : ew E 34 = w64 (cx_u cx + Z.of_nat o)) by exact (ew_Ereg_extra regs3 ex 2).
assert (Hs10 : 0 <= rd_s10 i s11 p3) by (unfold rd_s10; lia).
assert (U2 : bv_unsigned (ew E 2) = cx_F cx) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply c8_u64s; lia).
assert (U8 : bv_unsigned (ew E 8) = SHADOW_OFF)
  by (rewrite (EE 8%nat 8%bv eq_refl), R8; apply c8_u64s; unfold SHADOW_OFF; lia).
assert (U10 : bv_unsigned (ew E 10) = v) by (rewrite (EE 10%nat 10%bv eq_refl), R10; apply c8_u64s; lia).
assert (U19 : bv_unsigned (ew E 19) = cx_t cx + Z.of_nat (S p3) + Z.of_nat o)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; apply c8_u64s; lia).
assert (U26 : bv_unsigned (ew E 26) = rd_s10 i s11 p3)
  by (rewrite (EE 26%nat 26%bv eq_refl), R26; apply c8_u64s; unfold rd_s10 in *; lia).
assert (U32 : bv_unsigned (ew E 32) = (- rd_p0 cx i s11) mod 2 ^ 64)
  by (rewrite E32; apply c8_u64s; apply Z.mod_pos_bound; lia).
assert (U33 : bv_unsigned (ew E 33) = cx_u cx) by (rewrite E33; apply c8_u64s; lia).
assert (U34 : bv_unsigned (ew E 34) = cx_u cx + Z.of_nat o) by (rewrite E34; apply c8_u64s; lia).
assert (HS : st_ok tfibsegs E ss_c8B (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 RD_C9) mem3 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_c8B. apply entry_st_ok_full; try change (Ereg regs3 ex) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    apply (rd_frame_region_ok E _ (cx_F cx)); [exact U2 | lia | lia | |].
    + intros q Hq. apply (apresent_writable tfibsegs). apply Hpres. lia.
    + repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd Nat.add].
      * rewrite U32. exact V10.
      * rewrite U33. exact V20.
  - cbn. tauto.
  - split; [|split; [exact I|]].
    + cbn [f_atoms atoms_ok c8_atoms]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U2, U8. change (2 ^ 4) with 16. rewrite HFm, !Z.pow_0_r, !Z.mod_1_r.
      unfold SHADOW_OFF. repeat split; lia.
    + cbn [f_alias alias_ok c8_alB]. split; [|exact I].
      c8_alias. rewrite U19, U26, U32, U33, U34. c8_zmod. }
clearbody E.
assert (SHOK : sh_ok tfibsegs C8_Bx [] E
  (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 RD_C9) mem3 (seg_rom tfibsegs))))) by constructor.
pose proof (c8_kept_refl cx W3 mem3) as AV.
unfold cfg_at. change (w64 RD_C9) with (Z_to_bv 64 RD_C9).
change (unpoison [] mem3) with mem3 in HJ.
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 RD_C9) mem3 (seg_rom tfibsegs))) in HJ.
srr_branch_tok rd_tbl_ok HS SHOK C8_Bspan.
- (* v <> 0: matches is false, back to L at S close *)
  rewrite branch_ne_U, U_SOff, U_SLit, U10 in Hc. apply Bool.negb_true_iff, Z.eqb_neq in Hc.
  unfold zcanon, M64 in Hc. rewrite Z.add_0_r, !Z.mod_small in Hc by lia.
  aj_run_to_tok rd_tbl_ok HS HJ SHOK C8_Bspan RD_L.
  { c8_awr U2. }
  c8_avw U2. c8_mk HS.
  eapply (SL cx (S (S p3 + o))%nat d ly3 S3 W3 _ _ _ HB).
  split; [|split; [|split]].
  + eapply (c8_loop_kept B CTX cx d ly3 S3 W3 regs3 mem3 md3 _ _ _ HB HL HJ AV); c8_greg HS EE.
  + eapply c8_acc_next; [exact HA | exact Hi | rewrite (c8_decl _ _ _ _ _ _ HD), Hfo; reflexivity | | lia | lia].
    apply c8_nm_neq. intros Heq. apply Hc. apply Hvs. apply c8_strn; [lia | rewrite length_skipn; lia |].
    symmetry. exact Heq.
  + c8_rr HS. reflexivity.
  + c8_rr HS. rewrite U19. unfold w64. f_equal. lia.
- (* v = 0: local = uri + o into slot 0x38, strlen (local) *)
  rewrite branch_ne_U, U_SOff, U_SLit, U10 in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
  unfold zcanon, M64 in Hc. rewrite Z.add_0_r, !Z.mod_small in Hc by lia.
  aj_run_tok rd_tbl_ok HS HJ SHOK C8_Bspan.
  { c8_awr U2. }
  c8_avw U2.
  lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
    let r := eval vm_compute in (nth 0 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
    pose proof (g3_st_ok_region_nth Ex ssx (restrict _ msX) 0 r HS ltac:(vm_compute; reflexivity)) as HR0;
    cbn [ms_mem restrict] in HR0 end.
  pose proof (g3_field_of_region E _ 2 (cx_F cx) _ _ _ _ _ 0x38 8%N (SOff 34 0) (cx_u cx + Z.of_nat o) HR0 U2
    ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite U34, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as V38.
  cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V38. clear HR0.
  rreg HS (1%bv : bv 5) Q1. rreg HS (2%bv : bv 5) Q2. rreg HS (3%bv : bv 5) Q3. rreg HS (4%bv : bv 5) Q4.
  rreg HS (10%bv : bv 5) Q10.
  assert (HL1 : rd_loop B cx d ly3 S3 W3 (ms_regs ms) (ms_mem ms)
    (with_vm_backing (m_vm_lazy md3) mat md3)).
  { eapply (c8_loop_kept B CTX cx d ly3 S3 W3 regs3 mem3 md3 _ _ _ HB HL HJ AV); c8_greg HS EE. }
  pose proof HL1 as ((_ & _ & _ & _ & _ & _ & _ & _ & HRO1 & _ & Cu1 & _ & _) & _).
  c8_mk HS.
  eapply SRr_bind.
  { eapply (g3_aj_ro_at B LAWS PC_strlen STK_RT_STR (fun x => x = Z.of_nat (length (skipn o (cx_ub cx))))
      W3 (ms_regs ms) (ms_mem ms) (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx)
      (cx_mem cx) (cx_md cx) [] ly3 S3 _ EV_names (-224) (Z_to_bv 64 0x81f70) HJ).
    - unfold spZ. rewrite Q2, U2. lia.
    - reflexivity.
    - lia.
    - unfold ESTACK. lia.
    - lia.
    - rewrite Q3, (EE 3%nat 3%bv eq_refl), R3. exact Hgp.
    - rewrite Q4, (EE 4%nat 4%bv eq_refl), R4. exact Htp.
    - exact Q1.
    - vm_compute. reflexivity.
    - intros HPK. apply (STRLEN ly3 S3 W3 (ms_regs ms) (ms_mem ms) _ (cx_u cx + Z.of_nat o) (skipn o (cx_ub cx)) HPK).
      + exact (proj1 (IMG ly3 S3 W3 (ms_mem ms) _ (proj1 HJ) HRO1)).
      + rewrite Q10, E34. reflexivity.
      + apply c8_cstr_ok_skipn; [exact Cu1 | lia]. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & n & -> & HJ2 & HP2 & H10n & Hn & Hnl & Hfr2 & Hpres2).
  change (mkCfg (mkst regs2 (Z_to_bv 64 532336) mem2 (seg_rom tfibsegs)) md2)
    with (cfg_at tfibsegs RD_C10 regs2 mem2 md2).
  assert (AV2 : rd_kept cx W3 mem3 mem2).
  { apply (c8_call_kept cx W3 mem3 (ms_mem ms) mem2 AV). intros a Ha Hna. apply Hfr2; [exact Ha|].
    intros Hw. apply Hna. rewrite HF. lia. }
  assert (Hsp2 : getr regs2 2 = getr (ms_regs ms) 2) by exact (HP2 2 ltac:(unfold acallee_saved; lia)).
  apply (c8_segC f SL SPL cx i d s11 p1 p2 p3 o ly3 S3 W3 regs2 mem2 md2 HB).
  unfold rd_c10. cbv zeta.
  split.
  { eapply (c8_loop_kept B CTX cx d ly3 S3 W3 regs3 mem3 md3 _ _ _ HB HL HJ2 AV2).
    - rewrite Hsp2. c8_greg HS EE.
    - c8_cs HP2 HS. apply EE. reflexivity.
    - c8_cs HP2 HS. apply EE. reflexivity.
    - c8_cs HP2 HS. apply EE. reflexivity.
    - c8_cs HP2 HS. apply EE. reflexivity.
    - c8_cs HP2 HS. apply EE. reflexivity. }
  split; [exact HA|]. split; [exact Hi|]. split; [exact HD|]. split; [exact Hfo|]. split; [exact Hou|].
  split.
  { symmetry. apply (proj1 (c8_strn o (cx_ub cx) (skipn (S p3) (cx_tb cx)) ltac:(lia) ltac:(rewrite length_skipn; lia))).
    apply Hvs. exact Hc. }
  split.
  { unfold rd_slots_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. split; [|lia].
    apply (g3_val_mem_kept W3 W3 (ms_mem ms) mem2); [exact V38|]. intros q Hq. cbn in Hq.
    apply Hfr2; [lia|]. rewrite HF. lia. }
  split; [c8_cs HP2 HS; rewrite (EE 19%nat 19%bv eq_refl); exact R19|].
  split; [c8_cs HP2 HS; rewrite (EE 20%nat 20%bv eq_refl); exact R20|].
  split; [c8_cs HP2 HS; rewrite (EE 21%nat 21%bv eq_refl); exact R21|].
  split; [c8_cs HP2 HS; rewrite (EE 22%nat 22%bv eq_refl); exact R22|].
  split; [c8_cs HP2 HS; rewrite (EE 23%nat 23%bv eq_refl); exact R23|].
  split; [c8_cs HP2 HS; rewrite (EE 24%nat 24%bv eq_refl); exact R24|].
  split; [c8_cs HP2 HS; rewrite (EE 25%nat 25%bv eq_refl); exact R25|].
  split; [c8_cs HP2 HS; rewrite (EE 26%nat 26%bv eq_refl); exact R26|].
  split; [c8_cs HP2 HS; rewrite (EE 27%nat 27%bv eq_refl); exact R27|].
  rewrite H10n, Hnl, length_skipn. reflexivity.
Qed.

(* ---- A, 0x81f20 (rd_C8): r = strchr (ns, '>') ---- *)
Theorem rd_C8_holds : forall f, rd_seg_L B CTX f -> (forall m, rd_seg_PL B CTX (S f) m) -> rd_seg_C8 B CTX (S f).
Proof.
intros f SL SPL cx i d s11 p1 p2 p3 r ly3 S3 W3 regs3 mem3 md3 HB HC.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (c8_bounds B CTX cx HB) as (Bs1 & Bs2 & Bs3).
assert (FFR : STK_readings = 16624) by reflexivity. assert (FRT : STK_RT_STR = 8192) by reflexivity.
assert (HF : cx_F cx = cx_sp cx - 208) by reflexivity.
assert (HFm : cx_F cx mod 16 = 0).
{ rewrite HF. replace (cx_sp cx - 208) with (cx_sp cx + (-13) * 16) by lia. rewrite Z_mod_plus_full. exact Bs3. }
pose proof HB as (HAN & _).
pose proof HAN as (_ & _ & _ & Hgp & Htp & _).
destruct HC as (HL & HA & Hi & HD & HSL2 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & R10 & Hr).
pose proof HL as ((HJ & Hk & R2 & R3 & R4 & R8 & _ & _ & HRO & Ct & Cu & _ & _) & R9 & R18 & HSL & HVrp & HPm & HGl
  & Hcf & Hub0 & _ & Hd16).
pose proof Ct as (_ & Ht4 & Htc & _).
pose proof Cu as (_ & Hu4 & Huc & _).
pose proof HD as (Hh & Hs11 & Hsp & E1 & E2 & Hc58 & E3 & Hc60 & Hp3).
unfold rd_slots_ok, rd_loc_list in HSL.
apply Forall_cons_iff in HSL as [_ HSL]. apply Forall_cons_iff in HSL as [_ HSL].
apply Forall_cons_iff in HSL as [_ HSL]. apply Forall_cons_iff in HSL as [(V20 & _) HSL].
apply Forall_cons_iff in HSL as [(V30 & _) _]. cbn [fst snd] in V20, V30.
pose proof HSL2 as HSL2'. unfold rd_slots_ok in HSL2'.
apply Forall_cons_iff in HSL2' as [_ HSL2']. apply Forall_cons_iff in HSL2' as [(V28 & _) HSL2'].
apply Forall_cons_iff in HSL2' as [(V38 & _) _]. cbn [fst snd] in V28, V38.
assert (Hrr : 0 <= r < 2 ^ 64).
{ destruct Hr as [(-> & _) | (j & (Hj & _) & ->)]; [lia|]. rewrite length_skipn in Hj. lia. }
assert (Hs10 : 0 <= rd_s10 i s11 p3) by (unfold rd_s10; lia).
set (ex := map w64 [cx_u cx; cx_t cx + Z.of_nat (S p3); cx_ulen cx; rd_p0 cx i s11;
                    r - rd_p0 cx i s11 - rd_s10 i s11 p3 - 2]).
set (E := Ereg regs3 ex).
assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs3 q)
  by (intros n q Hn; apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = w64 (cx_u cx)) by exact (ew_Ereg_extra regs3 ex 0).
assert (E33 : ew E 33 = w64 (cx_t cx + Z.of_nat (S p3))) by exact (ew_Ereg_extra regs3 ex 1).
assert (E34 : ew E 34 = w64 (cx_ulen cx)) by exact (ew_Ereg_extra regs3 ex 2).
assert (E35 : ew E 35 = w64 (rd_p0 cx i s11)) by exact (ew_Ereg_extra regs3 ex 3).
assert (E36 : ew E 36 = w64 (r - rd_p0 cx i s11 - rd_s10 i s11 p3 - 2)) by exact (ew_Ereg_extra regs3 ex 4).
assert (U2 : bv_unsigned (ew E 2) = cx_F cx) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply c8_u64s; lia).
assert (U8 : bv_unsigned (ew E 8) = SHADOW_OFF)
  by (rewrite (EE 8%nat 8%bv eq_refl), R8; apply c8_u64s; unfold SHADOW_OFF; lia).
assert (U10 : bv_unsigned (ew E 10) = r) by (rewrite (EE 10%nat 10%bv eq_refl), R10; apply c8_u64s; lia).
assert (U26 : bv_unsigned (ew E 26) = rd_s10 i s11 p3)
  by (rewrite (EE 26%nat 26%bv eq_refl), R26; apply c8_u64s; unfold rd_s10 in *; lia).
assert (U32 : bv_unsigned (ew E 32) = cx_u cx) by (rewrite E32; apply c8_u64s; lia).
assert (U33 : bv_unsigned (ew E 33) = cx_t cx + Z.of_nat (S p3)) by (rewrite E33; apply c8_u64s; lia).
assert (U34 : bv_unsigned (ew E 34) = cx_ulen cx) by (rewrite E34; apply c8_u64s; unfold cx_ulen; lia).
assert (U35 : bv_unsigned (ew E 35) = rd_p0 cx i s11) by (rewrite E35; apply c8_u64s; unfold rd_p0; lia).
assert (U36 : bv_unsigned (ew E 36) = (r - rd_p0 cx i s11 - rd_s10 i s11 p3 - 2) mod 2 ^ 64)
  by (rewrite E36; apply c8_u64).
assert (HS : st_ok tfibsegs E ss_c8A (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 RD_C8) mem3 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_c8A. apply entry_st_ok_full; try change (Ereg regs3 ex) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    apply (rd_frame_region_ok E _ (cx_F cx)); [exact U2 | lia | lia | intros q Hq; lia |].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd Nat.add].
    + rewrite U32. exact V20.
    + rewrite U33. exact V28.
    + rewrite U34. exact V30.
    + rewrite U35. exact V38.
  - cbn. tauto.
  - split; [|split; [exact I|]].
    + cbn [f_atoms atoms_ok c8_atoms]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U2, U8. change (2 ^ 4) with 16. rewrite HFm, !Z.pow_0_r, !Z.mod_1_r.
      unfold SHADOW_OFF. repeat split; lia.
    + cbn [f_alias alias_ok c8_alA]. split; [|exact I].
      c8_alias. rewrite U10, U26, U35, U36. c8_zmod. }
clearbody E.
assert (SHOK : sh_ok tfibsegs C8_Bx [] E
  (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 RD_C8) mem3 (seg_rom tfibsegs))))) by constructor.
pose proof (c8_kept_refl cx W3 mem3) as AV.
unfold cfg_at. change (w64 RD_C8) with (Z_to_bv 64 RD_C8).
change (unpoison [] mem3) with mem3 in HJ.
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 RD_C8) mem3 (seg_rom tfibsegs))) in HJ.
destruct Hr as [(Hr0 & Hnin) | (j & Hj & Hrj)].
- (* r = 0: no '>' after ns, decl is DCut, the scan answers 0 *)
  srr_branch_tok rd_tbl_ok HS SHOK C8_Bspan.
  2:{ exfalso. rewrite branch_eq_U, U_SOff, U_SLit, U10, Hr0 in Hc. discriminate Hc. }
  aj_run_to_tok rd_tbl_ok HS HJ SHOK C8_Bspan RD_R.
  { awr_ok_tac. }
  c8_avk. c8_mk HS.
  assert (HL1 : rd_loop B cx d ly3 S3 W3 (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3)).
  { eapply (c8_loop_kept B CTX cx d ly3 S3 W3 regs3 mem3 md3 _ _ _ HB HL HJ AV); c8_greg HS EE. }
  pose proof (c8_decl _ _ _ _ _ _ HD) as Hdc. rewrite (c8_find_none _ _ Hnin) in Hdc.
  destruct (c8_acc_cut cx i d f HA Hi Hdc) as (Hnm & Hnr).
  pose proof HL1 as (HC1 & _ & _ & _ & HVrp1 & HPm1 & HGl1 & _).
  eapply (rd_ret_holds B CTX cx EV_names ly3 S3 W3 (ms_regs ms) (ms_mem ms) _ 0 HB HC1).
  + c8_rr HS. reflexivity.
  + lia.
  + split; [exact HPm1|]. split.
    * right. right. split; [exact Hub0|]. split; [exact Hcf|]. split; [symmetry; exact Hnm|].
      unfold cx_ulen in HGl1. exact HGl1.
    * assert (Hl0 : (length (cx_ub cx) =? 0)%nat = false).
      { apply Nat.eqb_neq. intros H0. apply length_zero_iff_nil in H0. exact (Hub0 H0). }
      rewrite Hl0, (proj2 (Z.eqb_neq _ _) Hcf). cbn [orb]. rewrite Hnr. exact HVrp1.
- (* r = ns + o *)
  pose proof Hj as (Hjl & _ & _). rewrite length_skipn in Hjl.
  pose proof (c8_find_first _ _ _ Hj) as Hfo.
  assert (U36' : bv_unsigned (ew E 36) = Z.of_nat j).
  { rewrite U36, Hrj. unfold rd_p0, rd_s10. replace (cx_t cx + Z.of_nat (S p3) + Z.of_nat j - _ - _ - 2)
      with (Z.of_nat j) by lia. apply Z.mod_small. lia. }
  srr_branch_tok rd_tbl_ok HS SHOK C8_Bspan.
  { exfalso. rewrite branch_eq_U, U_SOff, U_SLit, U10 in Hc. apply Z.eqb_eq in Hc. unfold zcanon, M64 in Hc.
    rewrite !Z.mod_small in Hc by lia. lia. }
  clear Hc. aj_run_tok rd_tbl_ok HS HJ SHOK C8_Bspan.
  { awr_ok_tac. }
  c8_avk.
  srr_branch_tok rd_tbl_ok HS SHOK C8_Bspan.
  + (* o >= uri_len: matches is false, back to L at S close *)
    rewrite branch_geu_U, !U_SOff, U36', U34 in Hc. apply Bool.negb_true_iff, Z.ltb_ge in Hc.
    unfold zcanon, M64, cx_ulen in Hc. rewrite !Z.add_0_r, !Z.mod_small in Hc by lia.
    aj_run_to_tok rd_tbl_ok HS HJ SHOK C8_Bspan RD_L.
    { awr_ok_tac. }
    c8_avk. c8_mk HS.
    eapply (SL cx (S (S p3 + j))%nat d ly3 S3 W3 _ _ _ HB).
    split; [|split; [|split]].
    * eapply (c8_loop_kept B CTX cx d ly3 S3 W3 regs3 mem3 md3 _ _ _ HB HL HJ AV); c8_greg HS EE.
    * eapply c8_acc_next; [exact HA | exact Hi | rewrite (c8_decl _ _ _ _ _ _ HD), Hfo; reflexivity | | lia | lia].
      apply c8_nm_len. lia.
    * c8_rr HS. reflexivity.
    * c8_rr HS. rewrite U10, Hrj. unfold w64. f_equal. lia.
  + (* o < uri_len: strncmp (uri, ns, o) *)
    rewrite branch_geu_U, !U_SOff, U36', U34 in Hc. apply Bool.negb_false_iff, Z.ltb_lt in Hc.
    unfold zcanon, M64, cx_ulen in Hc. rewrite !Z.add_0_r, !Z.mod_small in Hc by lia.
    aj_run_tok rd_tbl_ok HS HJ SHOK C8_Bspan.
    { awr_ok_tac. }
    c8_avk. clear ms. rename ms0 into ms.
    rreg HS (1%bv : bv 5) Q1. rreg HS (2%bv : bv 5) Q2. rreg HS (3%bv : bv 5) Q3. rreg HS (4%bv : bv 5) Q4.
    rreg HS (10%bv : bv 5) Q10. rreg HS (11%bv : bv 5) Q11. rreg HS (12%bv : bv 5) Q12.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?mdX) _ =>
      assert (HL1 : rd_loop B cx d ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdX) end.
    { eapply (c8_loop_kept B CTX cx d ly3 S3 W3 regs3 mem3 md3 _ _ _ HB HL HJ AV); c8_greg HS EE. }
    pose proof HL1 as ((_ & _ & _ & _ & _ & _ & _ & _ & HRO1 & Ct1 & Cu1 & _ & _) & _).
    c8_mk HS.
    eapply SRr_bind.
    { eapply (g3_aj_ro_at B LAWS PC_strncmp STK_RT_STR
        (fun x => x = 0 <-> FMH_Rt.strn_eq (Z.to_nat (Z.of_nat j)) (cx_ub cx) (skipn (S p3) (cx_tb cx)))
        W3 (ms_regs ms) (ms_mem ms) (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx)
        (cx_mem cx) (cx_md cx) [] ly3 S3 _ EV_names (-224) (Z_to_bv 64 0x81f4c) HJ).
      - unfold spZ. rewrite Q2, U2. lia.
      - reflexivity.
      - lia.
      - unfold ESTACK. lia.
      - lia.
      - rewrite Q3, (EE 3%nat 3%bv eq_refl), R3. exact Hgp.
      - rewrite Q4, (EE 4%nat 4%bv eq_refl), R4. exact Htp.
      - exact Q1.
      - vm_compute. reflexivity.
      - intros HPK. apply (STRNCMP ly3 S3 W3 (ms_regs ms) (ms_mem ms) _ (cx_u cx) (cx_t cx + Z.of_nat (S p3))
          (Z.of_nat j) (cx_ub cx) (skipn (S p3) (cx_tb cx)) HPK).
        + exact (proj1 (IMG ly3 S3 W3 (ms_mem ms) _ (proj1 HJ) HRO1)).
        + exact (proj1 (proj2 (IMG ly3 S3 W3 (ms_mem ms) _ (proj1 HJ) HRO1))).
        + rewrite Q10, E32. reflexivity.
        + rewrite Q11, E33. reflexivity.
        + rewrite Q12, E36, Hrj. unfold w64, rd_p0, rd_s10. f_equal. lia.
        + lia.
        + exact Cu1.
        + exact (c8_cstr_ok_skipn W3 (ms_mem ms) (cx_t cx) (cx_tb cx) (S p3) Ct1 ltac:(lia)). }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & H10v & Hv & HRv & Hfr2 & Hpres2).
    change (mkCfg (mkst regs2 (Z_to_bv 64 532300) mem2 (seg_rom tfibsegs)) md2)
      with (cfg_at tfibsegs RD_C9 regs2 mem2 md2).
    assert (AV2 : rd_kept cx W3 mem3 mem2).
    { apply (c8_call_kept cx W3 mem3 (ms_mem ms) mem2 AV). intros a Ha Hna. apply Hfr2; [exact Ha|].
      intros Hw. apply Hna. rewrite HF. lia. }
    assert (Hsp2 : getr regs2 2 = getr (ms_regs ms) 2) by exact (HP2 2 ltac:(unfold acallee_saved; lia)).
    apply (c8_segB f SL SPL cx i d s11 p1 p2 p3 j v ly3 S3 W3 regs2 mem2 md2 HB).
    unfold rd_c9. cbv zeta.
    split.
    { eapply (c8_loop_kept B CTX cx d ly3 S3 W3 regs3 mem3 md3 _ _ _ HB HL HJ2 AV2).
      - rewrite Hsp2. c8_greg HS EE.
      - c8_cs HP2 HS. apply EE. reflexivity.
      - c8_cs HP2 HS. apply EE. reflexivity.
      - c8_cs HP2 HS. apply EE. reflexivity.
      - c8_cs HP2 HS. apply EE. reflexivity.
      - c8_cs HP2 HS. apply EE. reflexivity. }
    split; [exact HA|]. split; [exact Hi|]. split; [exact HD|]. split; [exact Hfo|]. split; [unfold cx_ulen in *; lia|].
    split.
    { apply (c8_slots_kept B CTX cx W3 mem3 mem2 _ HB AV2).
      - apply Forall_cons; [|apply Forall_nil]. cbn [fst]. lia.
      - unfold rd_slots_ok in HSL2 |- *. apply Forall_cons; [exact (Forall_inv HSL2) | apply Forall_nil]. }
    split; [c8_cs HP2 HS; rewrite (EE 10%nat 10%bv eq_refl), R10, Hrj; reflexivity|].
    split; [c8_cs HP2 HS; rewrite (EE 20%nat 20%bv eq_refl); exact R20|].
    split; [c8_cs HP2 HS; rewrite (EE 21%nat 21%bv eq_refl); exact R21|].
    split; [c8_cs HP2 HS; rewrite (EE 22%nat 22%bv eq_refl); exact R22|].
    split; [c8_cs HP2 HS; rewrite (EE 23%nat 23%bv eq_refl); exact R23|].
    split; [c8_cs HP2 HS; rewrite (EE 24%nat 24%bv eq_refl); exact R24|].
    split; [c8_cs HP2 HS; rewrite (EE 25%nat 25%bv eq_refl); exact R25|].
    split; [c8_cs HP2 HS; rewrite (EE 26%nat 26%bv eq_refl); exact R26|].
    split; [c8_cs HP2 HS; rewrite (EE 27%nat 27%bv eq_refl); exact R27|].
    split; [exact H10v|]. split; [exact Hv|]. rewrite Nat2Z.id in HRv. exact HRv.
Qed.
End c.
