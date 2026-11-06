From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_repacer.fuzz_egress Require Statements.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Reusable Require Import
  YK11 YM05 YO0d YO09 YP09 YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL0g YL0i YL0k YL0s YN03 YN2b YN33 DriverSlots.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib Require Import
  ZTraceSpec ZComplete ZAllocator Contract FrameAPI FrameSlotG SlotKept SlotTopK.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require Mem.
Import ListNotations.
Open Scope Z_scope.
Section BridgeK.
Context {fx : FPState} {rc : RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis TBL : forall L A mem md, aa_MR API L A mem md -> forall a, static_owned B a -> 0 <= a < 2 ^ 64 ->
  Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = true -> mbyte (ms_segs B) mem a = seg_rom (ms_segs B) (Z_to_bv 64 a).
Lemma lib_post_x_T_of_t : forall G stk L A regs mem md p n b l T T' L' A' regs' mem' md',
  lib_post_t B API TD G stk L A regs mem md p n b l T T' L' A' regs' mem' md' ->
  lib_post_x_T B API G [] stk L A regs mem md p n b l T T' L' A' regs' mem' md'.
Proof using.
  intros G stk L A regs mem md p n b l T T' L' A' regs' mem' md'
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & _ & H11 & H12 & H13 & H14 & H15 & H16 & _ & H17 & H18 & H19 & H20).
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10
    (conj H11 (conj H12 (conj H13 (conj H14 (conj H15 (conj H16 (conj H17 (conj H18 (conj H19 H20))))))))))))))))))).
Qed.
Lemma lib_contract_x_T_of_t : forall G R GI j pc ra empty stk,
  lib_contract_t B API TD G R GI j pc ra empty stk -> lib_contract_x_T B API G R GI (fun _ => []) j pc ra empty stk.
Proof using TBL.
  intros G R GI j pc ra empty stk H L A regs mem md p n pl b T K Hpre HGI HTL HpT HR Hfrm HK.
  apply (H L A regs mem md p n pl b T K Hpre HGI HTL HpT HR (ro_agree_of_pre_x B API TBL stk empty L A regs mem md ra p n pl b Hpre)
    (lib_pre_x_sp B API stk empty L A regs mem md ra p n pl b Hpre) Hfrm).
  intros l c' (fx' & L' & A' & regs' & mem' & md' & T' & Hc & Hf & Hp & HGI').
  apply HK. exists fx', L', A', regs', mem', md', T'. split; [exact Hc|]. split; [exact Hf|].
  split; [exact (lib_post_x_T_of_t G stk L A regs mem md p n b l T T' L' A' regs' mem' md' Hp) | exact HGI'].
Qed.
End BridgeK.
Definition kept_shape : lib_shape := {|
  LIBK := fun pl fs K => K (LL 0 fs []);
  LIBK_ext := fun pl fs K K' H => H (LL 0 fs []);
  lib_delta := fun n b => b;
  lib_room := fun b n => sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 31 /\ sb_cap b = CAPMAX |}.
Lemma kept_permitted : shape_permitted kept_shape.
Proof. intros pl fs K HK. exact (HK _). Qed.
Lemma kept_room_text : forall T, (length T <= TBMAX)%nat -> (forall t k, In (t, k) T -> 0 < k <= TBBYTES) ->
  sb_live (TD [] T SBD) <= 64 /\ 0 <= sb_bytes (TD [] T SBD) <= 2 ^ 31 /\ sb_cap (TD [] T SBD) = CAPMAX.
Proof.
  intros T HL HK. unfold TBMAX in HL. unfold TBBYTES in HK.
  destruct T as [|[t1 k1] [|[t2 k2] [|x T]]]; cbn [length] in HL; [| | | lia].
  - unfold TD, SBD. cbn [fold_left sb_live sb_bytes sb_cap]. lia.
  - pose proof (HK t1 k1 (or_introl eq_refl)).
    unfold TD, SBD, sb_malloc. cbn [fold_left snd sb_live sb_bytes sb_cap]. lia.
  - pose proof (HK t1 k1 (or_introl eq_refl)). pose proof (HK t2 k2 (or_intror (or_introl eq_refl))).
    unfold TD, SBD, sb_malloc. cbn [fold_left snd sb_live sb_bytes sb_cap]. lia.
Qed.
Lemma kept_room : TB_room kept_shape.
Proof. intros T HL HK n. exact (kept_room_text T HL HK). Qed.
Theorem plain_halts_of_frame_slot_k : forall (G : list (Z * Z))
    (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop),
  (forall a, in_globals G a -> in_globals frame_G a) ->
  G_local_t src0_msyms G GI ->
  (forall mem, G_img_c src0_msyms G mem -> GI 0%nat [] mem) ->
  TB_bound GI ->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_t fx rc kept_shape src0_msyms (@zlib_API rc) src0_sink_head src0_sink
       TD G frame_RELRO GI j ENTRY RA_LIB EMPTY SLOT_STACK) ->
  Statements.plain_halts.
Proof.
  intros G GI HG GIL GI0 HB H.
  apply (plain_halts_from_slot_T kept_shape G frame_RELRO GI (fun _ => []) kept_permitted (fun _ _ => eq_refl) kept_room
    (fun a h => frame_G_src0 a (HG a h)) frame_RELRO_src0 GIL GI0 HB).
  intros rc fx j Hj.
  exact (lib_contract_x_T_of_t src0_msyms (@zlib_API rc) (zlib_tables rc) G frame_RELRO GI j _ _ _ _ (H rc fx j Hj)).
Qed.
