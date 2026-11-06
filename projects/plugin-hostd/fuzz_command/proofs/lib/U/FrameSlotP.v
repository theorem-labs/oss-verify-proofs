From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.plugin_hostd.fuzz_command Require Statements.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import
  YK11 YM05 YM02 YO0i YO0d YO05 YO06 YO09 YP09 YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL0g YL0i YL0k YL0s YN03 YN2b YN33
  DriverPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import
  ZTraceSpec ZComplete ZAllocator Contract FrameAPI FrameSlotG SlotKept SlotTopR AllocPack SlotPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
Import ListNotations.
Open Scope Z_scope.
Definition lv_fold (x : Z) (T : list (Z * Z)) (L : list Z) : list Z :=
  fold_left (fun L t => lv_add L (band (snd t)) x) T L.
Definition tsum (T : list (Z * Z)) : Z := fold_right (fun t s => snd t + s) 0 T.
Lemma live_fold_malloc : forall T b, pb_live (fold_left (fun b t => pb_malloc b (snd t)) T b) = lv_fold 1 T (pb_live b).
Proof. induction T as [|t T IH]; intros b; [reflexivity|]. cbn [fold_left]. rewrite IH. reflexivity. Qed.
Lemma live_fold_free : forall T b, pb_live (fold_left (fun b t => pb_free b (snd t)) T b) = lv_fold (-1) T (pb_live b).
Proof. induction T as [|t T IH]; intros b; [reflexivity|]. cbn [fold_left]. rewrite IH. reflexivity. Qed.
Lemma bytes_fold_malloc : forall T b, pb_bytes (fold_left (fun b t => pb_malloc b (snd t)) T b) = pb_bytes b + tsum T.
Proof.
  induction T as [|t T IH]; intros b; [cbn; lia|]. cbn [fold_left]. rewrite IH.
  change (tsum (t :: T)) with (snd t + tsum T). unfold pb_malloc. cbn [pb_bytes]. lia.
Qed.
Lemma bytes_fold_free : forall T b, pb_bytes (fold_left (fun b t => pb_free b (snd t)) T b) = pb_bytes b - tsum T.
Proof.
  induction T as [|t T IH]; intros b; [cbn; lia|]. cbn [fold_left]. rewrite IH.
  change (tsum (t :: T)) with (snd t + tsum T). unfold pb_free. cbn [pb_bytes]. lia.
Qed.
Lemma lv_fold_add : forall x T L a y, lv_add (lv_fold x T L) a y = lv_fold x T (lv_add L a y).
Proof.
  intros x T. induction T as [|t T IH]; intros L a y; [reflexivity|].
  unfold lv_fold in *. cbn [fold_left]. rewrite IH. f_equal. apply lv_add_comm.
Qed.
Lemma lv_fold_cancel : forall T L, lv_fold (-1) T (lv_fold 1 T L) = L.
Proof.
  induction T as [|t T IH]; intros L; [reflexivity|].
  change (lv_fold (-1) (t :: T) (lv_fold 1 (t :: T) L)) with
    (lv_fold (-1) T (lv_add (lv_fold 1 T (lv_add L (band (snd t)) 1)) (band (snd t)) (-1))).
  rewrite lv_fold_add, lv_add_cancel by lia. apply IH.
Qed.
Lemma TDP_live : forall T T' b, pb_live (TDP T T' b) = lv_fold 1 T' (lv_fold (-1) T (pb_live b)).
Proof. intros T T' b. unfold TDP. rewrite live_fold_malloc, live_fold_free. reflexivity. Qed.
Lemma TDP_bytes : forall T T' b, pb_bytes (TDP T T' b) = pb_bytes b - tsum T + tsum T'.
Proof. intros T T' b. unfold TDP. rewrite bytes_fold_malloc, bytes_fold_free. lia. Qed.
Lemma TDP_chain : forall T T' b d, pb_live b = pb_live (TDP [] T d) -> pb_bytes b = pb_bytes (TDP [] T d) ->
  pb_live (TDP T T' b) = pb_live (TDP [] T' d) /\ pb_bytes (TDP T T' b) = pb_bytes (TDP [] T' d).
Proof.
  intros T T' b d H1 H2. rewrite !TDP_live, !TDP_bytes in *. rewrite H1, H2.
  change (lv_fold (-1) [] (pb_live d)) with (pb_live d). change (tsum []) with 0.
  rewrite lv_fold_cancel. split; [reflexivity | lia].
Qed.
Definition RI_P (CS : list byte -> list Z) (pl : list byte) (j : nat) (T : list (Z * Z)) (A : astate) : Prop :=
  exists d caps, drv_pb d /\ length caps = 49%nat /\ (forall k, 0 <= k < 49 -> PCAP0 <= znth k caps <= znth k (CS pl)) /\
  res_ok_pack A (PB (pb_live (TDP [] T d)) (pb_bytes (TDP [] T d)) caps).
Section BridgeP.
Context {fx : FPState} {rc : RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis TBL : forall L A mem md, aa_MR API L A mem md -> forall a, static_owned B a -> 0 <= a < 2 ^ 64 ->
  Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = true -> mbyte (ms_segs B) mem a = seg_rom (ms_segs B) (Z_to_bv 64 a).
Lemma ro_agree_of_pre_w : forall stk empty L A regs mem md ra p n pl,
  lib_pre_w B API stk empty L A regs mem md ra p n pl -> ro_agree (ms_segs B) mem.
Proof using TBL.
  intros stk empty L A regs mem md ra p n pl [Hpre _].
  unfold lib_pre in Hpre. pose proof Hpre as [HMR _].
  apply (ro_agree_of_rodata_ok B mem); [| exact (TBL L A mem md HMR)].
  repeat match type of Hpre with _ /\ ?R => destruct Hpre as [_ Hpre] end. exact Hpre.
Qed.
Lemma lib_pre_w_sp : forall stk empty L A regs mem md ra p n pl,
  lib_pre_w B API stk empty L A regs mem md ra p n pl -> spZ regs <= TASK_SIZE.
Proof using.
  intros stk empty L A regs mem md ra p n pl H. unfold lib_pre_w in H.
  repeat match type of H with _ /\ ?R => destruct H as [_ H] end. unfold TASK_SIZE. lia.
Qed.
Lemma lib_post_x_R_of_p : forall cs G stk L A regs mem md p n b l T T' L' A' regs' mem' md',
  lib_post_p B API cs G stk L A regs mem md p n b l T T' L' A' regs' mem' md' ->
  lib_post_x_R B API G [] stk L A regs mem md p n l T T' L' A' regs' mem' md' /\
  res_ok_pack A' (PB (pb_live (TDP T T' b)) (pb_bytes (TDP T T' b)) cs).
Proof using.
  intros cs G stk L A regs mem md p n b l T T' L' A' regs' mem' md'
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & _ & H12 & H13 & H14 & H15 & H16 & H17 & _ & H19 & H20 & H21 & H22).
  split; [|exact H19].
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10
    (conj H12 (conj H13 (conj H14 (conj H15 (conj H16 (conj H17 (conj H20 (conj H21 H22)))))))))))))))))).
Qed.
Lemma lib_contract_x_R_of_p : forall CS G R GI j pc ra empty stk, CS_ok CS ->
  lib_contract_p B API CS G R GI j pc ra empty stk ->
  lib_contract_x_R B API (RI_P CS) G R GI (fun _ => []) j pc ra empty stk.
Proof using TBL.
  intros CS G R GI j pc ra empty stk HCS H L A regs mem md p n pl T K Hpre (d & caps & Hd & Hlen & Hcap & Hres)
    HGI HTL HpT HR Hfrm HK.
  apply (H L A regs mem md p n pl (PB (pb_live (TDP [] T d)) (pb_bytes (TDP [] T d)) caps) T K Hpre Hres
    (conj Hlen (conj Hcap (ex_intro _ d (conj Hd (conj eq_refl eq_refl))))) HGI HTL HpT HR
    (ro_agree_of_pre_w stk empty L A regs mem md ra p n pl Hpre) (lib_pre_w_sp stk empty L A regs mem md ra p n pl Hpre) Hfrm).
  intros l c' (fx' & L' & A' & regs' & mem' & md' & T' & Hc & Hf & Hp & HGI').
  destruct (lib_post_x_R_of_p (CS pl) G stk L A regs mem md p n _ l T T' L' A' regs' mem' md' Hp) as [Hp' Hres'].
  destruct (TDP_chain T T' (PB (pb_live (TDP [] T d)) (pb_bytes (TDP [] T d)) caps) d eq_refl eq_refl) as [E1 E2].
  rewrite E1, E2 in Hres'. destruct (HCS pl) as [HC1 HC2].
  apply HK. exists fx', L', A', regs', mem', md', T'. split; [exact Hc|]. split; [exact Hf|].
  split; [exact Hp'|]. split; [|exact HGI'].
  exists d, (CS pl). split; [exact Hd|]. split; [exact HC1|]. split; [|exact Hres'].
  intros k Hk. split; [exact (HC2 k Hk) | lia].
Qed.
End BridgeP.
Lemma lib_contract_x_R_all_of_p {rc : RunCeil} {LS : lib_shape} (B : malloc_syms) (API : AllocAPI B) {SH : sink_head} {SK : sink_syms}
  (TBL : forall L A mem md, aa_MR API L A mem md -> forall a, static_owned B a -> 0 <= a < 2 ^ 64 ->
    Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = true -> mbyte (ms_segs B) mem a = seg_rom (ms_segs B) (Z_to_bv 64 a))
  (CS : list byte -> list Z) (G R : list (Z * Z)) (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop)
  (pc ra empty stk : Z) : CS_ok CS ->
  (forall (fx : FPState) (j : nat), (j < 4)%nat -> @lib_contract_p fx rc LS B API SH SK CS G R GI j pc ra empty stk) ->
  lib_contract_x_R_all B API (RI_P CS) G R GI (fun _ => []) pc ra empty stk.
Proof. intros HCS H fx j Hj. exact (lib_contract_x_R_of_p B API TBL CS G R GI j pc ra empty stk HCS (H fx j Hj)). Qed.
Lemma permitted_of_LIBK : forall (LS : lib_shape), (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) -> shape_permitted LS.
Proof. intros LS H pl fs K HK. rewrite H. exact (HK _). Qed.
Lemma driver_RI_P : forall CS, CS_ok CS -> forall data, leaves (run_RI (RI_P CS) (YO06.payload data)) (driver_tree data).
Proof.
  intros CS HCS data. eapply leaves_mono; [| exact (driver_pack data)].
  intros [dl A] H. unfold run_RI. cbn [fst snd] in *. destruct dl; cbv beta iota in H |- *; try exact I.
  destruct H as (d & Hd & HA). destruct (HCS (YO06.payload data)) as [HC1 HC2].
  exists d, (repeat 64 49). split; [exact Hd|]. split; [reflexivity|]. split; [|exact HA].
  intros k Hk. rewrite (proj2 (pk0_ok k Hk)). pose proof (HC2 k Hk). unfold PCAP0 in *. lia.
Qed.
Theorem plain_halts_of_frame_slot_p : forall (LS : lib_shape) (CS : list byte -> list Z) (G : list (Z * Z))
    (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop),
  (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) ->
  (forall a, in_globals G a -> in_globals frame_G a) ->
  G_local_t src0_msyms G GI ->
  (forall mem, G_img_c src0_msyms G mem -> GI 0%nat [] mem) ->
  TB_bound GI ->
  CS_ok CS ->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_p fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink CS G frame_RELRO GI j ENTRY RA_LIB EMPTY SLOT_STACK) ->
  Statements.ubsan_halts.
Proof.
  intros LS CS G GI HL HG GIL GI0 _ HCS H.
  apply (plain_halts_from_slot_R LS (RI_P CS) G frame_RELRO GI (fun _ => []) (permitted_of_LIBK LS HL)
    (driver_RI_P CS HCS) (fun a h => frame_G_src0 a (HG a h)) frame_RELRO_src0 GIL GI0).
  intros rc. exact (lib_contract_x_R_all_of_p src0_msyms (@zlib_API rc) (zlib_tables rc) CS G frame_RELRO GI _ _ _ _ HCS (H rc)).
Qed.
Theorem plain_halts_of_frame_slot_pg : forall (LS : lib_shape) (CS : list byte -> list Z) (G : list (Z * Z))
    (GI : nat -> (word -> option byte) -> Prop),
  (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) ->
  (forall a, in_globals G a -> in_globals frame_G a) ->
  G_local_c src0_msyms G GI ->
  (forall mem, G_img_c src0_msyms G mem -> GI 0%nat mem) ->
  CS_ok CS ->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_pg fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink CS G frame_RELRO GI j ENTRY RA_LIB EMPTY SLOT_STACK) ->
  Statements.ubsan_halts.
Proof.
  intros LS CS G GI HL HG GIL GI0 HCS H.
  apply (plain_halts_from_slot_R LS (RI_P CS) G frame_RELRO (fun j T m => T = [] /\ GI j m) (fun _ => [])
    (permitted_of_LIBK LS HL) (driver_RI_P CS HCS) (fun a h => frame_G_src0 a (HG a h)) frame_RELRO_src0
    (G_local_T_of_G src0segs G GI GIL) (fun mem Hm => conj eq_refl (GI0 mem Hm))).
  intros rc. apply (lib_contract_x_R_all_of_p src0_msyms (@zlib_API rc) (zlib_tables rc) CS G frame_RELRO _ _ _ _ _ HCS).
  intros fx j Hj. exact (lib_contract_p_of_pg src0_msyms (@zlib_API rc) CS G frame_RELRO GI j _ _ _ _ (H rc fx j Hj)).
Qed.
