From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.reac_pw.fuzz_role Require Statements Images.
From OSSVerify.reac_pw.fuzz_role.images Require Import Plain.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import
  YK11 YK15 YM05 YM02 YM0b YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots YO0d_cf YL0i_cfw.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require Import
  ZImage ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Contract FrameAPI FrameSlotG
  SlotAgree AllocCf Agree AgreeWalk.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Mem.
Import ListNotations.
Open Scope Z_scope.

Section BridgeCg.
Context {fx : FPState} {rc : RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis TBL : forall L A mem md, aa_MR API L A mem md -> forall a, static_owned B a -> 0 <= a < 2 ^ 64 ->
  Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = true -> mbyte (ms_segs B) mem a = seg_rom (ms_segs B) (Z_to_bv 64 a).
Lemma lib_contract_x_Rc_of_cg : forall G G' R R' GI j pc ra empty stk, (j < 4)%nat ->
  (forall a, in_globals G a -> in_globals G' a) ->
  (forall a, in_globals R a -> in_globals R' a) ->
  lib_contract_cg B API G R GI j pc ra empty stk ->
  lib_contract_x_Rc B API (@RI_G LS) G' R' (fun j T m => T = [] /\ GI j m) (fun _ => []) j pc ra empty stk.
Proof using TBL.
  intros G G' R R' GI j pc ra empty stk Hj HG HRR H L A regs mem md p n pl T K Hpre HRI [HT HGI] _ _ HR Hfrm HK.
  subst T.
  pose proof Hpre as (_ & Hn & _).
  destruct (@RI_G_step LS GI j Hj pl [] A mem HRI (conj eq_refl HGI)) as (b & Hb & Hroom & Hnext).
  rewrite <- Hn in Hroom, Hnext.
  pose proof (lib_pre_x_of_w B API stk empty L A regs mem md ra p n pl b Hpre Hb Hroom) as Hx.
  apply (H L A regs mem md p n pl b K Hx HGI (G_img_mono _ R R' mem HRR HR)
    (ro_agree_of_pre_x B API TBL stk empty L A regs mem md ra p n pl b Hx)
    (lib_pre_x_sp B API stk empty L A regs mem md ra p n pl b Hx) Hfrm).
  intros l c' (fx' & L' & A' & regs' & mem' & md' & Hc & Hf & Hp & HGI').
  destruct (lib_post_x_R_of_T B API G [] stk L A regs mem md p n b l [] [] L' A' regs' mem' md'
    (lib_post_x_T_of_G B API G [] stk L A regs mem md p n b l L' A' regs' mem' md'
      (lib_post_x_G_of_g B API G stk L A regs mem md p n b l L' A' regs' mem' md' Hp))) as [HpR Hres].
  apply HK. exists fx', L', A', regs', mem', md', []. split; [exact Hc|]. split; [exact Hf|].
  split; [exact (lib_post_x_R_mono B API G G' [] stk L A regs mem md p n l [] [] L' A' regs' mem' md' HG HpR)|].
  split; [exact (Hnext [] A' mem' Hres (conj eq_refl HGI')) | exact (conj eq_refl HGI')].
Qed.
End BridgeCg.

Lemma lib_contract_x_Rc_all_of_cg {rc : RunCeil} {LS : lib_shape} (B : malloc_syms) (API : AllocAPI B)
  {SH : sink_head} {SK : sink_syms}
  (TBL : forall L A mem md, aa_MR API L A mem md -> forall a, static_owned B a -> 0 <= a < 2 ^ 64 ->
    Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = true -> mbyte (ms_segs B) mem a = seg_rom (ms_segs B) (Z_to_bv 64 a))
  (G G' R R' : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop) (pc ra empty stk : Z) :
  (forall a, in_globals G a -> in_globals G' a) ->
  (forall a, in_globals R a -> in_globals R' a) ->
  (forall (fx : FPState) (j : nat), (j < 4)%nat -> @lib_contract_cg fx rc LS B API SH SK G R GI j pc ra empty stk) ->
  lib_contract_x_Rc_all B API (@RI_G LS) G' R' (fun j T m => T = [] /\ GI j m) (fun _ => []) pc ra empty stk.
Proof.
  intros HG HRR H fx j Hj.
  exact (lib_contract_x_Rc_of_cg B API TBL G G' R R' GI j pc ra empty stk Hj HG HRR (H fx j Hj)).
Qed.

Definition SBD_AG : sbound := SB 2 (2 ^ 28) CAP_AG.

Lemma driver_slots_AG data : leaves (run_slots SBD_AG) (driver_tree data).
Proof.
  eapply leaves_mono; [| exact (leaves_and _ _ _ (driver_res data) (driver_inv data))].
  intros [d s] [HR HI]. unfold run_slots, drv_inv in *. cbn [fst snd] in *.
  destruct d; try exact I. destruct HI as ((HW & HS & HG & HN & HNR & HM) & Hnb & Hub).
  destruct HR as (HII & _ & _ & Hh & _).
  unfold res_ok_slots, SBD_AG, HCAP, CAP_AG, DRB in *. cbn [sb_live sb_bytes sb_cap rb_hand] in *.
  repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
Qed.

Lemma driver_RI_AG : forall (LS : lib_shape), (forall data, @room_calls LS (payload_len data) (calls data) SBD_AG) ->
  forall data, leaves (run_RI (@RI_G LS) (payload data)) (driver_tree data).
Proof.
  intros LS HROOM data. eapply leaves_mono; [| exact (driver_slots_AG data)].
  intros [d A] H. unfold run_slots, run_RI in *. cbn [fst snd] in *. destruct d; cbv beta iota in H |- *; try exact I.
  exists SBD_AG. split; [exact H|].
  destruct (calls_witness (Z.of_nat (length (YO06.payload data))) (Nat2Z.is_nonneg _)) as (d' & Hd1 & Hd2).
  pose proof (HROOM d') as Hr. rewrite Hd1, Hd2 in Hr. exact Hr.
Qed.

Lemma RI_G_res : forall (LS : lib_shape) pl j T A, @RI_G LS pl j T A -> exists b, res_ok_slots A b.
Proof. intros LS pl j T A (b & Hb & _). exists b. exact Hb. Qed.

Lemma zlib_limit : forall (rc : RunCeil) L A mem md, aa_MR (@zlib_API rc) L A mem md ->
  SRC_LIM_MIN <= vm_limit (m_vmmaps md).
Proof.
  intros rc L A mem md H. change (MRx src0_msyms L A mem md) in H.
  exact (lg_limit _ _ _ _ (mc_ledger _ _ _ _ _ (MRx_MRc _ _ _ _ _ H))).
Qed.

#[local] Existing Instance YK11.fx0.

Theorem zlib_walk_crealizes : forall (rc : RunCeil) (LS : lib_shape)
    (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop) (OUT : list byte -> list byte),
  (forall data, @room_calls LS (payload_len data) (calls data) SBD_AG) ->
  G_local_T src0segs src0_G GI ->
  (forall mem, G_img src0segs src0_G mem -> GI 0%nat [] mem) ->
  lib_contract_x_Rc_all src0_msyms (@zlib_API rc) (@RI_G LS) src0_G src0_R GI OUT LIBPC RA_LIB EMPTY LIB_STACK ->
  forall sp brk mbase rnd lim inp,
  valid_sp sp -> valid_brk src0segs brk -> valid_mmap_base mbase ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  valid_input inp -> SRC_LIM_MIN <= lim ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  YM05.rc_lim = lim ->
  crealizes src0_msyms (init_config src0segs Plain_init_pc Plain_phdrs sp brk mbase rnd lim inp) (SPECX (LS:=LS) inp).
Proof.
  intros rc LS GI OUT HROOM GIL GI0 LIBXc.
  exact (@plain_walk_crealizes rc LS (@zlib_API rc) zlib_allocator_extra GI (@RI_G LS) OUT GIL GI0 LIBXc
    driver_obligationsX_proved (driver_RI_AG LS HROOM) (fun fx' => @zlib_free_contract_cf fx' rc)
    (zlib_tables rc) (@RI_G_res LS) (fun fx' => @src0_malloc_realizes_cf fx' rc)
    (fun fx' => @src0_free_realizes_cf fx' rc) (zlib_limit rc)).
Qed.

Theorem plain_crealizes_of_cg : forall (LS : lib_shape) (G : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop),
  (forall data, @room_calls LS (payload_len data) (calls data) SBD_AG) ->
  (forall a, in_globals G a -> in_globals frame_G a) ->
  G_local_c src0_msyms G GI ->
  (forall mem, G_img_c src0_msyms G mem -> GI 0%nat mem) ->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_cg fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
       G frame_RELRO GI j ENTRY RA_LIB EMPTY SLOT_STACK) ->
  forall en inp lim, valid_entry Images.plain en inp -> valid_input inp -> SRC_LIM_MIN <= lim ->
    rz_run Images.plain lim en inp (SPECX (LS:=LS) inp) /\ cf_run Images.plain lim en inp.
Proof.
  intros LS G GI HROOM HG GIL GI0 H [sp brk0 mbase rnd] inp lim Hentry Hinput Hlim.
  apply (valid_entry_sv48 _ _ inp (valid_input_va_size inp Hinput)) in Hentry.
  destruct Hentry as [Hsp [Hbrk [Hmb Hfits]]].
  set (rc := RunCeilOf (bv_unsigned sp) (valid_sp_window_for_ceil sp Hsp) lim).
  assert (HG' : forall a, in_globals G a -> in_globals src0_G a) by (intros a h; exact (frame_G_src0 a (HG a h))).
  change (crealizes src0_msyms (init_config src0segs Plain_init_pc Plain_phdrs sp brk0 mbase rnd lim inp)
    (SPECX (LS:=LS) inp)).
  apply (zlib_walk_crealizes rc LS (fun j T m => T = [] /\ GI j m) (fun _ => []) HROOM
    (G_local_T_mono src0segs G src0_G _ HG' (G_local_T_of_G src0segs G GI GIL))
    (fun mem Hm => conj eq_refl (GI0 mem (G_img_mono src0segs G src0_G mem HG' Hm)))
    (lib_contract_x_Rc_all_of_cg src0_msyms (@zlib_API rc) (zlib_tables rc) G src0_G frame_RELRO src0_R GI
      LIBPC RA_LIB EMPTY LIB_STACK HG' frame_RELRO_src0 (H rc))
    sp brk0 mbase rnd lim inp Hsp Hbrk Hmb Hfits Hinput Hlim).
  unfold rc. apply ceil_of_top_run.
  unfold rc. reflexivity.
Qed.
