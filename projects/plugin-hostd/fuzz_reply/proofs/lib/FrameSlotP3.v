From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.plugin_hostd.fuzz_reply Require Statements.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
  YK11 YM05 YM02 YO0i YO0d YO05 YO06 YO09 YP09 YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL0g YL0i YL0k YL0s YN03 YN2b YN33
  DriverPack DriverPack3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import
  ZTraceSpec ZComplete ZAllocator Contract FrameAPI FrameSlotG SlotKept SlotTopR AllocPack SlotPack AllocPack3 SlotPack3
  FrameSlotP.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
Import ListNotations.
Open Scope Z_scope.
Definition RI_P3 (CS : list byte -> list Z) (MC : list Z) (pl : list byte) (j : nat) (T : list (Z * Z)) (A : astate) : Prop :=
  exists d caps, drv_pb d /\ length caps = 49%nat /\ (forall k, 0 <= k < 49 -> PCAP0 <= znth k caps <= znth k (CS pl)) /\
  res_ok_pack3 A (PB3 (pb_live (TDP [] T d)) (pb_bytes (TDP [] T d)) caps [] MC).
Section BridgeP3.
Context {fx : FPState} {rc : RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis TBL : forall L A mem md, aa_MR API L A mem md -> forall a, static_owned B a -> 0 <= a < 2 ^ 64 ->
  Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = true -> mbyte (ms_segs B) mem a = seg_rom (ms_segs B) (Z_to_bv 64 a).
Lemma lib_post_x_R_of_p3 : forall cs MC G stk L A regs mem md p n b l T T' L' A' regs' mem' md',
  lib_post_p3 B API cs MC G stk L A regs mem md p n b l T T' L' A' regs' mem' md' ->
  lib_post_x_R B API G [] stk L A regs mem md p n l T T' L' A' regs' mem' md' /\
  res_ok_pack3 A' (PB3 (pb_live (TDP T T' (pb_of3 b))) (pb_bytes (TDP T T' (pb_of3 b))) cs [] MC).
Proof using.
  intros cs MC G stk L A regs mem md p n b l T T' L' A' regs' mem' md'
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & _ & H12 & H13 & H14 & H15 & H16 & H17 & _ & H19 & H20 & H21 & H22).
  split; [|exact H19].
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10
    (conj H12 (conj H13 (conj H14 (conj H15 (conj H16 (conj H17 (conj H20 (conj H21 H22)))))))))))))))))).
Qed.
Lemma lib_contract_x_R_of_p3 : forall CS MC G R GI j pc ra empty stk, CS_ok CS ->
  lib_contract_p3 B API CS MC G R GI j pc ra empty stk ->
  lib_contract_x_R B API (RI_P3 CS MC) G R GI (fun _ => []) j pc ra empty stk.
Proof using TBL.
  intros CS MC G R GI j pc ra empty stk HCS H L A regs mem md p n pl T K Hpre (d & caps & Hd & Hlen & Hcap & Hres)
    HGI HTL HpT HR Hfrm HK.
  apply (H L A regs mem md p n pl (PB3 (pb_live (TDP [] T d)) (pb_bytes (TDP [] T d)) caps [] MC) T K Hpre Hres
    (conj (conj Hlen (conj Hcap (ex_intro _ d (conj Hd (conj eq_refl eq_refl))))) eq_refl) eq_refl HGI HTL HpT HR
    (ro_agree_of_pre_w B API TBL stk empty L A regs mem md ra p n pl Hpre)
    (lib_pre_w_sp B API stk empty L A regs mem md ra p n pl Hpre) Hfrm).
  intros l c' (fx' & L' & A' & regs' & mem' & md' & T' & Hc & Hf & Hp & HGI').
  destruct (lib_post_x_R_of_p3 (CS pl) MC G stk L A regs mem md p n _ l T T' L' A' regs' mem' md' Hp) as [Hp' Hres'].
  destruct (TDP_chain T T' (pb_of3 (PB3 (pb_live (TDP [] T d)) (pb_bytes (TDP [] T d)) caps [] MC)) d eq_refl eq_refl)
    as [E1 E2].
  rewrite E1, E2 in Hres'. destruct (HCS pl) as [HC1 HC2].
  apply HK. exists fx', L', A', regs', mem', md', T'. split; [exact Hc|]. split; [exact Hf|].
  split; [exact Hp'|]. split; [|exact HGI'].
  exists d, (CS pl). split; [exact Hd|]. split; [exact HC1|]. split; [|exact Hres'].
  intros k Hk. split; [exact (HC2 k Hk) | lia].
Qed.
End BridgeP3.
Lemma lib_contract_x_R_all_of_p3 {rc : RunCeil} {LS : lib_shape} (B : malloc_syms) (API : AllocAPI B) {SH : sink_head} {SK : sink_syms}
  (TBL : forall L A mem md, aa_MR API L A mem md -> forall a, static_owned B a -> 0 <= a < 2 ^ 64 ->
    Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = true -> mbyte (ms_segs B) mem a = seg_rom (ms_segs B) (Z_to_bv 64 a))
  (CS : list byte -> list Z) (MC : list Z) (G R : list (Z * Z)) (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop)
  (pc ra empty stk : Z) : CS_ok CS ->
  (forall (fx : FPState) (j : nat), (j < 4)%nat -> @lib_contract_p3 fx rc LS B API SH SK CS MC G R GI j pc ra empty stk) ->
  lib_contract_x_R_all B API (RI_P3 CS MC) G R GI (fun _ => []) pc ra empty stk.
Proof. intros HCS H fx j Hj. exact (lib_contract_x_R_of_p3 B API TBL CS MC G R GI j pc ra empty stk HCS (H fx j Hj)). Qed.
Lemma driver_RI_P3 : forall CS, CS_ok CS -> forall data,
  leaves (run_RI (RI_P3 CS frame_MCAP) (YO06.payload data)) (driver_tree data).
Proof.
  intros CS HCS data. eapply leaves_mono; [| exact (driver_pack3 data)].
  intros [dl A] H. unfold run_RI. cbn [fst snd] in *. destruct dl; cbv beta iota in H |- *; try exact I.
  destruct H as (d & Hd & HA). destruct (HCS (YO06.payload data)) as [HC1 HC2].
  exists d, (repeat 64 49). split; [exact Hd|]. split; [reflexivity|]. split; [|exact HA].
  intros k Hk. rewrite (proj2 (pk0_ok k Hk)). pose proof (HC2 k Hk). unfold PCAP0 in *. lia.
Qed.
Theorem plain_halts_of_frame_slot_p3 : forall (LS : lib_shape) (CS : list byte -> list Z) (G : list (Z * Z))
    (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop),
  (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) ->
  (forall a, in_globals G a -> in_globals frame_G a) ->
  G_local_t src0_msyms G GI ->
  (forall mem, G_img_c src0_msyms G mem -> GI 0%nat [] mem) ->
  TB_bound GI ->
  CS_ok CS ->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_p3 fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink CS frame_MCAP G frame_RELRO GI j
       ENTRY RA_LIB EMPTY SLOT_STACK) ->
  Statements.plain_halts.
Proof.
  intros LS CS G GI HL HG GIL GI0 _ HCS H.
  apply (plain_halts_from_slot_R LS (RI_P3 CS frame_MCAP) G frame_RELRO GI (fun _ => []) (permitted_of_LIBK LS HL)
    (driver_RI_P3 CS HCS) (fun a h => frame_G_src0 a (HG a h)) frame_RELRO_src0 GIL GI0).
  intros rc. exact (lib_contract_x_R_all_of_p3 src0_msyms (@zlib_API rc) (zlib_tables rc) CS frame_MCAP G frame_RELRO GI
    _ _ _ _ HCS (H rc)).
Qed.
