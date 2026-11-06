From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_repacer.fuzz_lock Require Statements.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import
  YK11 YM05 YO0d YO09 YP09 YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL0g YL0i YL0k YL0s YN03 YN2b YN33.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib Require Import
  ZTraceSpec ZComplete ZAllocator SlotTopG Contract FrameAPI.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Mem.
Import ListNotations.
Open Scope Z_scope.
Section Bridge.
Context {fx : FPState} {rc : RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis TBL : forall L A mem md, aa_MR API L A mem md -> forall a, static_owned B a -> 0 <= a < 2 ^ 64 ->
  Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = true -> mbyte (ms_segs B) mem a = seg_rom (ms_segs B) (Z_to_bv 64 a).
Lemma lib_post_x_G_of_g : forall G stk L A regs mem md p n b l L' A' regs' mem' md',
  lib_post_g B API G stk L A regs mem md p n b l L' A' regs' mem' md' ->
  lib_post_x_G B API G [] stk L A regs mem md p n b l L' A' regs' mem' md'.
Proof using.
  intros G stk L A regs mem md p n b l L' A' regs' mem' md'
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & _ & H11 & H12 & H13 & H14 & H15 & H16 & _ & H17 & H18).
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10
    (conj H11 (conj H12 (conj H13 (conj H14 (conj H15 (conj H16 (conj H17 H18))))))))))))))))).
Qed.
Lemma ro_agree_of_pre_x : forall stk empty L A regs mem md ra p n pl b,
  lib_pre_x B API stk empty L A regs mem md ra p n pl b -> ro_agree (ms_segs B) mem.
Proof using TBL.
  intros stk empty L A regs mem md ra p n pl b [Hpre _].
  unfold lib_pre in Hpre. pose proof Hpre as [HMR _].
  apply (ro_agree_of_rodata_ok B mem); [| exact (TBL L A mem md HMR)].
  repeat match type of Hpre with _ /\ ?R => destruct Hpre as [_ Hpre] end. exact Hpre.
Qed.
Lemma lib_contract_x_G_of_g : forall G R GI j pc ra empty stk,
  lib_contract_g B API G R GI j pc ra empty stk -> lib_contract_x_G B API G R GI (fun _ => []) j pc ra empty stk.
Proof using TBL.
  intros G R GI j pc ra empty stk H L A regs mem md p n pl b K Hpre HGI HR Hfrm HK.
  apply (H L A regs mem md p n pl b K Hpre HGI HR (ro_agree_of_pre_x stk empty L A regs mem md ra p n pl b Hpre)
    (lib_pre_x_sp B API stk empty L A regs mem md ra p n pl b Hpre) Hfrm).
  intros l c' (fx' & L' & A' & regs' & mem' & md' & Hc & Hf & Hp & HGI').
  apply HK. exists fx', L', A', regs', mem', md'. split; [exact Hc|]. split; [exact Hf|].
  split; [exact (lib_post_x_G_of_g G stk L A regs mem md p n b l L' A' regs' mem' md' Hp) | exact HGI'].
Qed.
End Bridge.
Definition ivls_sub_b (G G' : list (Z * Z)) : bool :=
  forallb (fun p => existsb (fun q => (fst q <=? fst p) && (fst p + snd p <=? fst q + snd q)) G') G.
Lemma ivls_sub_sound : forall G G' a, ivls_sub_b G G' = true -> in_globals G a -> in_globals G' a.
Proof.
  intros G G' a H (lo & len & Hin & Ha). unfold ivls_sub_b in H. rewrite forallb_forall in H.
  pose proof (H _ Hin) as Hx. apply existsb_exists in Hx as ((lo' & len') & Hin' & Hb). cbn [fst snd] in Hb.
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists lo', len'. split; [exact Hin' | lia].
Qed.
Lemma frame_G_src0 : forall a, in_globals frame_G a -> in_globals src0_G a.
Proof. intros a. apply ivls_sub_sound. vm_compute. reflexivity. Qed.
Lemma frame_RELRO_src0 : forall a, in_globals frame_RELRO a -> in_globals src0_R a.
Proof. intros a. apply ivls_sub_sound. vm_compute. reflexivity. Qed.
Lemma ro_false_range : forall segs lo len a,
  forallb (fun k => negb (Mem.ro_addr segs (Z_to_bv 64 (lo + Z.of_nat k)))) (seq 0 (Z.to_nat len)) = true ->
  lo <= a < lo + len -> Mem.ro_addr segs (Z_to_bv 64 a) = false.
Proof.
  intros segs lo len a H Ha. rewrite forallb_forall in H.
  assert (Hk : In (Z.to_nat (a - lo)) (seq 0 (Z.to_nat len))) by (apply in_seq; lia).
  specialize (H _ Hk). rewrite Z2Nat.id in H by lia.
  replace (lo + (a - lo)) with a in H by lia. apply negb_true_iff. exact H.
Qed.
Lemma zlib_tables : forall (rc : RunCeil) L A mem md, aa_MR (@zlib_API rc) L A mem md ->
  forall a, static_owned src0_msyms a -> 0 <= a < 2 ^ 64 ->
  Mem.ro_addr (ms_segs src0_msyms) (Z_to_bv 64 a) = true ->
  mbyte (ms_segs src0_msyms) mem a = seg_rom (ms_segs src0_msyms) (Z_to_bv 64 a).
Proof.
  intros rc L A mem md HMR a Hs Ha Hro.
  change (MRx src0_msyms L A mem md) in HMR.
  pose proof (mc_statics _ _ _ _ _ (proj1 HMR)) as ST.
  unfold static_owned in Hs.
  destruct Hs as [H|[H|[H|[H|[H|[H|Ht]]]]]].
  - exfalso. rewrite (ro_false_range (ms_segs src0_msyms) (ms_lock src0_msyms) 4 a ltac:(vm_compute; reflexivity) ltac:(lia)) in Hro. discriminate Hro.
  - exfalso. rewrite (ro_false_range (ms_segs src0_msyms) (ms_libc src0_msyms + 3) 1 a ltac:(vm_compute; reflexivity) ltac:(lia)) in Hro. discriminate Hro.
  - exfalso. rewrite (ro_false_range (ms_segs src0_msyms) (ms_libc src0_msyms + 8) 8 a ltac:(vm_compute; reflexivity) ltac:(lia)) in Hro. discriminate Hro.
  - exfalso. rewrite (ro_false_range (ms_segs src0_msyms) (ms_libc src0_msyms + 48) 8 a ltac:(vm_compute; reflexivity) ltac:(lia)) in Hro. discriminate Hro.
  - exfalso. rewrite (ro_false_range (ms_segs src0_msyms) (ms_got_guard src0_msyms) 8 a ltac:(vm_compute; reflexivity) ltac:(lia)) in Hro. discriminate Hro.
  - exfalso. rewrite (ro_false_range (ms_segs src0_msyms) (ms_guard src0_msyms) 8 a ltac:(vm_compute; reflexivity) ltac:(lia)) in Hro. discriminate Hro.
  - assert (Hv : table_addr src0_msyms a \/ vml_lo src0_msyms <= a < vml_lo src0_msyms + vml_len src0_msyms)
      by (unfold table_addr; tauto).
    destruct Hv as [Hv|Hv]; [apply (st_tables _ _ ST); exact Hv|].
    exfalso. rewrite (ro_false_range (ms_segs src0_msyms) (vml_lo src0_msyms) (vml_len src0_msyms) a ltac:(vm_compute; reflexivity) ltac:(lia)) in Hro. discriminate Hro.
Qed.
Theorem plain_halts_of_frame_slot : forall (G : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop),
  (forall a, in_globals G a -> in_globals frame_G a) ->
  G_local_c src0_msyms G GI ->
  (forall mem, G_img_c src0_msyms G mem -> GI 0%nat mem) ->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_g fx rc checksum_shape src0_msyms (@zlib_API rc) src0_sink_head src0_sink
       G frame_RELRO GI j ENTRY RA_LIB EMPTY SLOT_STACK) ->
  Statements.plain_halts.
Proof.
  intros G GI HG GIL GI0 H.
  apply (plain_halts_from_slot_G checksum_shape G frame_RELRO GI (fun _ => []) checksum_permitted
    (fun data => checksum_room_calls _ _) (fun a h => frame_G_src0 a (HG a h))).
  - exact frame_RELRO_src0.
  - exact GIL.
  - exact GI0.
  - intros rc fx j Hj.
    exact (lib_contract_x_G_of_g src0_msyms (@zlib_API rc) (zlib_tables rc) G frame_RELRO GI j _ _ _ _ (H rc fx j Hj)).
Qed.
