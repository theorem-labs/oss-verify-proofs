(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs: ported from reac-repacer/fuzz_uci proofs/reac-repacer/fuzz_uci/lib/Prog/LLVMFuzzerTestOneInput_c.v at bc49657c087a; module path, this image's values, LLVM_K from check_inject. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_egress/lib/Prog/LLVMFuzzerTestOneInput_c.v, with its module paths changed; 129 of its 145 lines of code are new or changed and 51 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/SlotPack.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_decode; no image value changed; module path OSSVerify.Proofs.libdiginet.fuzz_decode.lib. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/SlotPack.v; 127 of its 175 lines of code are new or changed and 97 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/SlotAgreeV.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_decode; no image value changed; module path OSSVerify.Proofs.libdiginet.fuzz_decode.lib. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Reusable Require Import
  YK15 YM06 YO0j YO0m YO03 YO0f YO0g YO0x YK0i YK0o YK0s YK0h YK14 YK1b YK1a YK1i YK0n YP0n YP0m YP02 YN3f
  YO0p YO0l YO0n YO0k YO0o YL01 YL00
  YK11 YM05 YM02 YO0i YO0d YO05 YO06 YO09 YP09 YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL0g YL0i YL0k YL0s YN03 YN2b YN33
  DriverSlots DriverPack YL0i_cfw.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import
  ZTraceSpec ZComplete ZAllocator Contract FrameAPI FrameSlotG SlotKept SlotTopR AllocPack SlotPack FrameSlotP
  OutForm FrameSlotO SlotAgree AgreeZlib AllocPackGSF.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Mem.
Import ListNotations.
Open Scope Z_scope.

(* Cut-free (crealizes) twins of the variant library slots: lib_contract_o (output on stderr) and the pack slots
   lib_contract_p / lib_contract_pg (pack resource form, carrying GSF in pre and post), and their bridges to the
   cut-free walk slot lib_contract_x_Rc. *)

Definition RI_Pc (CS : list byte -> list Z) (pl : list byte) (j : nat) (T : list (Z * Z)) (A : astate) : Prop :=
  RI_P CS pl j T A /\ GSF A.

Section Agree.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.

Definition lib_contract_cgo (f : list byte -> list byte) (G R : list (Z * Z))
    (GI : nat -> (word -> option byte) -> Prop) (j : nat) (pc ra empty stk : Z) : Prop :=
  forall L A regs mem md p n pl b (K : lleaf -> TSet),
    lib_pre_x B API stk empty L A regs mem md ra p n pl b ->
    fdchan (Z_to_bv 64 2) ch_stderr md ->
    GI j mem ->
    G_img_c B R mem ->
    ro_agree segs mem ->
    spZ regs <= TASK_SIZE ->
    frm_zero fp_csr ->
    (forall (l : lleaf) (c' : config),
       (exists (fx' : FPState) L' A' regs' mem' md',
          c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
          frm_zero (@fp_csr fx') /\
          lib_post_o B API (f pl) G stk L A regs mem md p n b l L' A' regs' mem' md' /\
          GI (S j) mem') ->
       crealizes B c' (K l)) ->
    crealizes B (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) (LIBK pl (m_fs md) K).

Definition lib_post_cgp (cs : list Z) (G : list (Z * Z)) (stk : Z) (L : layout) (A : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (p n : Z) (b : pbound) (l : lleaf) (T T' : list (Z * Z))
    (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  lib_post_p B API cs G stk L A regs mem md p n b l T T' L' A' regs' mem' md' /\ GSF A'.

Definition lib_contract_cgp (CS : list byte -> list Z) (G R : list (Z * Z))
    (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop) (j : nat)
    (pc ra empty stk : Z) : Prop :=
  forall L A regs mem md p n pl b T (K : lleaf -> TSet),
    lib_pre_w B API stk empty L A regs mem md ra p n pl ->
    rf_ok pack_cf_form A b ->
    pack_entry CS pl T b ->
    GI j T mem ->
    tb_live L A T ->
    (0 < n -> ~ In (p, n) T) ->
    G_img_c B R mem ->
    ro_agree segs mem ->
    spZ regs <= TASK_SIZE ->
    frm_zero fp_csr ->
    (forall (l : lleaf) (c' : config),
       (exists (fx' : FPState) L' A' regs' mem' md' T',
          c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
          frm_zero (@fp_csr fx') /\
          lib_post_cgp (CS pl) G stk L A regs mem md p n b l T T' L' A' regs' mem' md' /\
          GI (S j) T' mem') ->
       crealizes B c' (K l)) ->
    crealizes B (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) (LIBK pl (m_fs md) K).

Definition lib_post_cgpg (cs : list Z) (G : list (Z * Z)) (stk : Z) (L : layout) (A : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (p n : Z) (b : pbound) (l : lleaf)
    (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  lib_post_pg B API cs G stk L A regs mem md p n b l L' A' regs' mem' md' /\ GSF A'.

Definition lib_contract_cgpg (CS : list byte -> list Z) (G R : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop)
    (j : nat) (pc ra empty stk : Z) : Prop :=
  forall L A regs mem md p n pl b (K : lleaf -> TSet),
    lib_pre_w B API stk empty L A regs mem md ra p n pl ->
    rf_ok pack_cf_form A b ->
    pack_entry CS pl [] b ->
    GI j mem ->
    G_img_c B R mem ->
    ro_agree segs mem ->
    spZ regs <= TASK_SIZE ->
    frm_zero fp_csr ->
    (forall (l : lleaf) (c' : config),
       (exists (fx' : FPState) L' A' regs' mem' md',
          c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
          frm_zero (@fp_csr fx') /\
          lib_post_cgpg (CS pl) G stk L A regs mem md p n b l L' A' regs' mem' md' /\
          GI (S j) mem') ->
       crealizes B c' (K l)) ->
    crealizes B (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) (LIBK pl (m_fs md) K).

Lemma lib_contract_cgp_of_cgpg : forall CS G R GI j pc ra empty stk,
  lib_contract_cgpg CS G R GI j pc ra empty stk ->
  lib_contract_cgp CS G R (fun j T m => T = [] /\ GI j m) j pc ra empty stk.
Proof using.
  intros CS G R GI j pc ra empty stk H L A regs mem md p n pl b T K Hpre Hb He [HT HGI] _ _ HR Hro Hsp Hfrm HK.
  subst T.
  apply (H L A regs mem md p n pl b K Hpre Hb He HGI HR Hro Hsp Hfrm).
  intros l c' (fx' & L' & A' & regs' & mem' & md' & Hc & Hf & [Hp HG] & HGI').
  apply HK. exists fx', L', A', regs', mem', md', []. split; [exact Hc|]. split; [exact Hf|].
  split; [exact (conj (lib_post_p_of_pg B API (CS pl) G stk L A regs mem md p n b l L' A' regs' mem' md' Hp) HG)|].
  split; [reflexivity | exact HGI'].
Qed.

Hypothesis TBL : forall L A mem md, aa_MR API L A mem md -> forall a, static_owned B a -> 0 <= a < 2 ^ 64 ->
  Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = true -> mbyte (ms_segs B) mem a = seg_rom (ms_segs B) (Z_to_bv 64 a).

Lemma lib_contract_x_Rc_of_cgo : forall f G G' R R' GI j pc ra empty stk, (j < 4)%nat ->
  (forall a, in_globals G a -> in_globals G' a) ->
  (forall a, in_globals R a -> in_globals R' a) ->
  lib_contract_cgo f G R GI j pc ra empty stk ->
  lib_contract_x_Rc B API (@RI_G LS) G' R' (fun j T m => T = [] /\ GI j m) f j pc ra empty stk.
Proof using TBL.
  intros f G G' R R' GI j pc ra empty stk Hj HG HRR H L A regs mem md p n pl T K Hpre HRI [HT HGI] _ _ HR Hfrm HK.
  subst T.
  pose proof Hpre as (_ & Hn & _).
  destruct (@RI_G_step LS GI j Hj pl [] A mem HRI (conj eq_refl HGI)) as (b & Hb & Hroom & Hnext).
  rewrite <- Hn in Hroom, Hnext.
  pose proof (lib_pre_x_of_w B API stk empty L A regs mem md ra p n pl b Hpre Hb Hroom) as Hx.
  apply (H L A regs mem md p n pl b K Hx (lib_pre_x_fd B API stk empty L A regs mem md ra p n pl b Hx)
    HGI (G_img_mono _ R R' mem HRR HR)
    (ro_agree_of_pre_x B API TBL stk empty L A regs mem md ra p n pl b Hx)
    (lib_pre_x_sp B API stk empty L A regs mem md ra p n pl b Hx) Hfrm).
  intros l c' (fx' & L' & A' & regs' & mem' & md' & Hc & Hf & Hp & HGI').
  destruct (lib_post_x_R_of_T B API G (f pl) stk L A regs mem md p n b l [] [] L' A' regs' mem' md'
    (lib_post_x_T_of_G B API G (f pl) stk L A regs mem md p n b l L' A' regs' mem' md'
      (lib_post_x_G_of_o B API (f pl) G stk L A regs mem md p n b l L' A' regs' mem' md' Hp))) as [HpR Hres].
  apply HK. exists fx', L', A', regs', mem', md', []. split; [exact Hc|]. split; [exact Hf|].
  split; [exact (lib_post_x_R_mono B API G G' (f pl) stk L A regs mem md p n l [] [] L' A' regs' mem' md' HG HpR)|].
  split; [exact (Hnext [] A' mem' Hres (conj eq_refl HGI')) | exact (conj eq_refl HGI')].
Qed.

Lemma lib_contract_x_Rc_of_cgp : forall CS G R GI j pc ra empty stk, CS_ok CS ->
  lib_contract_cgp CS G R GI j pc ra empty stk ->
  lib_contract_x_Rc B API (RI_Pc CS) G R GI (fun _ => []) j pc ra empty stk.
Proof using TBL.
  intros CS G R GI j pc ra empty stk HCS H L A regs mem md p n pl T K Hpre [(d & caps & Hd & Hlen & Hcap & Hres) HGs]
    HGI HTL HpT HR Hfrm HK.
  apply (H L A regs mem md p n pl (PB (pb_live (TDP [] T d)) (pb_bytes (TDP [] T d)) caps) T K Hpre (conj Hres HGs)
    (conj Hlen (conj Hcap (ex_intro _ d (conj Hd (conj eq_refl eq_refl))))) HGI HTL HpT HR
    (ro_agree_of_pre_w B API TBL stk empty L A regs mem md ra p n pl Hpre)
    (lib_pre_w_sp B API stk empty L A regs mem md ra p n pl Hpre) Hfrm).
  intros l c' (fx' & L' & A' & regs' & mem' & md' & T' & Hc & Hf & [Hp HGs'] & HGI').
  destruct (lib_post_x_R_of_p B API (CS pl) G stk L A regs mem md p n _ l T T' L' A' regs' mem' md' Hp) as [Hp' Hres'].
  destruct (TDP_chain T T' (PB (pb_live (TDP [] T d)) (pb_bytes (TDP [] T d)) caps) d eq_refl eq_refl) as [E1 E2].
  rewrite E1, E2 in Hres'. destruct (HCS pl) as [HC1 HC2].
  apply HK. exists fx', L', A', regs', mem', md', T'. split; [exact Hc|]. split; [exact Hf|].
  split; [exact Hp'|]. split; [|exact HGI'].
  split; [|exact HGs'].
  exists d, (CS pl). split; [exact Hd|]. split; [exact HC1|]. split; [|exact Hres'].
  intros k Hk. split; [exact (HC2 k Hk) | lia].
Qed.

End Agree.

Lemma lib_contract_x_Rc_all_of_cgo {rc : YM05.RunCeil} (B : malloc_syms) (API : AllocAPI B)
  {SH : sink_head} {SK : sink_syms}
  (TBL : forall L A mem md, aa_MR API L A mem md -> forall a, static_owned B a -> 0 <= a < 2 ^ 64 ->
    Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = true -> mbyte (ms_segs B) mem a = seg_rom (ms_segs B) (Z_to_bv 64 a))
  (f : list byte -> list byte) (G G' R R' : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop) (pc ra empty stk : Z) :
  (forall a, in_globals G a -> in_globals G' a) ->
  (forall a, in_globals R a -> in_globals R' a) ->
  (forall (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_cgo fx rc (out_shape f) B API SH SK f G R GI j pc ra empty stk) ->
  @lib_contract_x_Rc_all rc (out_shape f) B API SH SK (@RI_G (out_shape f)) G' R' (fun j T m => T = [] /\ GI j m) f
    pc ra empty stk.
Proof.
  intros HG HRR H fx j Hj.
  exact (lib_contract_x_Rc_of_cgo B API TBL f G G' R R' GI j pc ra empty stk Hj HG HRR (H fx j Hj)).
Qed.

Lemma lib_contract_x_Rc_all_of_cgp {rc : YM05.RunCeil} {LS : lib_shape} (B : malloc_syms) (API : AllocAPI B)
  {SH : sink_head} {SK : sink_syms}
  (TBL : forall L A mem md, aa_MR API L A mem md -> forall a, static_owned B a -> 0 <= a < 2 ^ 64 ->
    Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = true -> mbyte (ms_segs B) mem a = seg_rom (ms_segs B) (Z_to_bv 64 a))
  (CS : list byte -> list Z) (G R : list (Z * Z)) (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop)
  (pc ra empty stk : Z) : CS_ok CS ->
  (forall (fx : FPState) (j : nat), (j < 4)%nat -> @lib_contract_cgp fx rc LS B API SH SK CS G R GI j pc ra empty stk) ->
  lib_contract_x_Rc_all B API (RI_Pc CS) G R GI (fun _ => []) pc ra empty stk.
Proof.
  intros HCS H fx j Hj. exact (lib_contract_x_Rc_of_cgp B API TBL CS G R GI j pc ra empty stk HCS (H fx j Hj)).
Qed.
