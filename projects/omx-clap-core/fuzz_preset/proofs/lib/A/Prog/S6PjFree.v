(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/pj_free_defs.v, with its module paths, module names and numbers changed; 437 of its 549 lines of code are new or changed and 94 lines of the source are left out. *)
(* fuzz_preset image A, slice S6 (WalkS6): pj_free's walk (108 instructions, recursive) over the ONE image-A program
   listing (lib/A/Listing_prog.v, h-verbs-1 v4), generic in the image facts (Context PAImg A_prog_listing), in the
   allocator relation ARx (LAWS : AR_laws_x .. cf_head) and in a memory invariant Pm (srr_inv_laws, srr_inv_call).
   THIS FILE: the statements and the shared glue of the walk's SEGMENTS (rule 24: proves no function; kind: statement
   text + segment glue). The segments are lib/A/Prog/S6PjFreeEnt.v (entry), S6PjFreeLH.v (loop head), S6PjFreeLKC.v (key,
   bound test) and S6PjFreeTail.v (after the loop, epilogue).
   THE ROOM POSITION IS ONE SEPARABLE PART, the OBSERVER of h-rw-man-5's image-B walk (lib/A/Prog/PjFreeCommon.v
   pf_obs / pf_reach / pf_safe, one copy for images A and B): each fuzz_free call adds one step of an abstract FX; the
   cuts carry pf_reach FX along the post-order list F (pj_foR), the entry carries pf_safe FX PB F. No segment depends
   on a fuzz_free room text: the callee is PjFreeCommon's tfuzz_free_specO PB FX. The HBulk form (PRH_FnPj.v:1105
   tpj_free_specX; a Theorem Labs lane's ruling 15:15Z) comes only at the composition (S6PjFreeTop.v pj_free_holds), which is not stated here.
   The walk's text is tpj_free_specOP below: PjFreeCommon's tpj_free_specO with the m-form post generalised to Pm
   (tpj_free_specO_of_P: the instance at memnorm).
   THE RE-HIDING MOVE: pj_free's run crosses fuzz_free, which can hide shadow again (YA0nH.wle'), so the text and every
   segment statement conclude SRr' SEGS RZ_cf, the walk's post pf_FIN is fpostW's R form at wle' SEGS RZ_cf, and the
   cuts (pf_LH, pf_LK, pf_LC, pf_LX, pf_EP) carry the frame's journal at wle' (pf_frameR (wle' SEGS RZ_cf)). The entry's
   journal starts at wle' (YCbqGcallW.ajournal_x_init_WR). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YCbqGcallW YC80xf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YC80xf_inv YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnReader PRH_FnAlloc PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger PRW_StepKit S6PjCommon.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PjStringCommon.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PjFreeCommon PjFreePure.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.


(* ======== the walk's text with the keep of a memory invariant P (generic over the listing and the image) ======== *)
Section xp. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg} {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation RZ_cf := (@YGcfRehidePost.RZ_cf rc).
(* PjFreeCommon's tpj_free_specO (the instrumented pj_free text, one copy for images A and B) with its m-form post
   fpostWmR .. Q = fpostWR .. (fQmn mem Q) generalised to fpostWR .. (fun .. => Q .. /\ (P mem -> P mem')), at
   wle' segs RZ_cf as tpj_free_specO *)
Definition tpj_free_specOP (P : (word -> option byte) -> Prop) (PB : astate -> Prop) (FX : pf_obs)
    (CTX0 : list (list Z)) (n : nat) : Prop :=
  forall most own ly S Hp W regs mem md ch d v D F Lam peak cnt fail ran,
  fpre B ARx (STK_pj_free n) ly S Hp W regs mem md ch ->
  prh_univ_closure B CTX0 -> room_live_cf S ->
  getr regs 10 = w64 v ->
  fwin ly W regs mem d ->
  (v = 0 /\ D = [] /\ F = [] \/
   v <> 0 /\ v < YM05.alloc_ceiling /\ pj_foR segs (rdW W mem) (prh_lin Lam) n v D F /\
   prhPj_slot B (STK_pj_free n) d ly S Lam W regs mem v) ->
  (v <> 0 -> pf_safe FX PB F ly S) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr' segs RZ_cf W (cfg_at segs (pa_sigma AS_pj_free) regs mem md)
    (fpostWR B ARx SK (wle' segs RZ_cf) (STK_pj_free n) d
       (if v =? 0 then [] else (v, v + 56) :: ablocks_fp (prhPj_hbl D))
       regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       (pf_K0post B D v ly S Hp Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' md' /\
        pf_reach FX F ly S [] ly' S') /\
       (P mem -> P mem'))).
Lemma tpj_free_specO_of_P : forall PB FX CTX0 n, tpj_free_specOP (YAkMemnorm.memnorm segs) PB FX CTX0 n ->
  tpj_free_specO B ARx SK PB FX CTX0 n.
Proof. intros PB FX CTX0 n H. exact H. Qed.
End xp.

(* ======== image A's numbers ======== *)
(* pj_free's offset in the listing (DERIVED: its slot times 4, PAImg_prog A_entry_pj_free) *)
Definition AF_pf : Z := 4 * Z.of_nat (A_prog_slot AS_pj_free).
Definition PF_Bx : sv := SOff 32 0.
Definition PF_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* ---- the entry seat: the own frame of 96 bytes below the entry sp (atom 2), the GOT word of the shadow base and the
   shadow-base cell ---- *)
Definition pf_regions : smem := [stack_region 96; got_regionP; bcell_regionP 32].
Definition pf_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_pf : sstate := mkSS AF_pf sr_atoms pf_regions None pf_facts.
(* ---- the seat at slot 13 (AF_pf + 52, v <> 0): the frame of the twelve saved registers (their own atoms: none is
   written yet), the GOT word and the cell, v's node (atom 10 = a0) with the header words the code reads (atoms 33 .. 36:
   str, kids, keys, n) ---- *)
Definition pf_saves1 : list (Z * nat) :=
  [(0, 26%nat); (8, 25%nat); (16, 24%nat); (24, 23%nat); (32, 22%nat); (40, 21%nat); (48, 20%nat); (56, 19%nat);
   (64, 18%nat); (72, 9%nat); (80, 8%nat); (88, 1%nat)].
Definition pf_frame1 : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 96 0 0 (map (fun c => YP09.mkChunk (fst c) (CVal 8 (SOff (snd c) 0))) pf_saves1).
Definition pf_node1 : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 56 0 0 [YP09.mkChunk 16 (CVal 8 (SOff 33 0)); YP09.mkChunk 24 (CVal 8 (SOff 34 0));
    YP09.mkChunk 32 (CVal 8 (SOff 35 0)); YP09.mkChunk 40 (CVal 8 (SOff 36 0))].
Definition pf_facts1 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 (2 ^ 47 - 56) 3);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_pf1 : sstate := mkSS (AF_pf + 52) sr_atoms [pf_frame1; got_regionP; bcell_regionP 32; pf_node1] None pf_facts1.
Definition PF_SH1 : list shent := [mkSHE 10 0 56].
(* ---- the tail's seat (any pc after the loop): s0 = v (atom 8), s4 = the shadow offset (atom 20, the run's Bx); s1 / s2 /
   s3 = v + 32 / v + 40 / v + 24 and s5 the cell of v + 40, as the code computed them; v's header words str / kids /
   keys / n as region chunks (atoms 32 .. 35); v's 56 bytes a shadow entry ---- *)
Definition pft_cell (x : sv) : sv := SAlu ALU_ADD (SAlu ALU_SRL x (SLit 3)) (SOff 20 0).
Definition pft_sregs : list sv :=
  Eval vm_compute in
  sr_set (sr_set (sr_set (sr_set sr_atoms 9%bv (SOff 8 32)) 18%bv (SOff 8 40)) 19%bv (SOff 8 24)) 21%bv (pft_cell (SOff 8 40)).
Lemma pft_sregs_eq : pft_sregs =
  sr_set (sr_set (sr_set (sr_set sr_atoms 9%bv (SOff 8 32)) 18%bv (SOff 8 40)) 19%bv (SOff 8 24)) 21%bv (pft_cell (SOff 8 40)).
Proof. vm_compute. reflexivity. Qed.
Definition pft_vhdr : YP09.region :=
  YP09.mkRegion (Some 8%nat) 0 56 0 0
    [YP09.mkChunk 16 (CVal 8 (SOff 32 0)); YP09.mkChunk 24 (CVal 8 (SOff 33 0));
     YP09.mkChunk 32 (CVal 8 (SOff 34 0)); YP09.mkChunk 40 (CVal 8 (SOff 35 0))].
Definition pft_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF 4096 (2 ^ 47 - 64) 3); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_pft (pc : Z) : sstate := mkSS pc pft_sregs [pft_vhdr] None pft_facts.
Definition PFT_Bx : sv := SOff 20 0.
Definition PFT_SH : list shent := [mkSHE 8 0 56].
Ltac pft_regne :=
  let E := fresh "E" in
  intros E; apply (f_equal (fun x : bv 5 => bv_unsigned x)) in E; vm_compute in E; discriminate E.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
Variable SK : YI16.sink_head.
Context {PA : PAImg A_prog_listing}.
#[local] Notation CP := CfParams_preset.
#[local] Abbreviation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val _ A_prog_listing PA).
#[local] Abbreviation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_A).
(* the fixed re-hideable zone of the cf layer (YGcfRehidePost.v) at this section's run ceiling *)
#[local] Notation RZ_cf := (@YGcfRehidePost.RZ_cf rc).

Definition pf_E (regs : bvmap 5 word) : env := @Eimg _ A_prog_listing PA (Ereg regs [Z_to_bv 64 SHADOW_OFF]).
Definition pf_E1 (regs : bvmap 5 word) (xs : list Z) : env :=
  @Eimg _ A_prog_listing PA (Ereg regs (Z_to_bv 64 SHADOW_OFF :: map (Z_to_bv 64) xs)).


(* ======== the walk's cuts (offsets from pj_free's entry AF_pf; DERIVED: the listing's slot differences times 4) ======== *)
Definition PF_LH : Z := 136.   (* slot 34, the loop head `lbu a0, 0(s9)` *)
Definition PF_LK : Z := 156.   (* slot 39, the recursive call's return site `lbu a0, 0(s10)` *)
Definition PF_LC : Z := 200.   (* slot 50, after the key's fuzz_free `lbu a0, 0(s5)` *)
Definition PF_LX : Z := 228.   (* slot 57, after the loop `srli a0, s3, 3` *)
Definition PF_EP : Z := 320.   (* slot 80, the epilogue `ld ra, 88(sp)` *)

Section c.
#[local] Existing Instance prh_img_A.
#[local] Existing Instance CfParams_preset.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable Pm : (word -> option byte) -> Prop.
Variable CTX0 : list (list Z).
(* the observer of the fuzz_free calls and what each call asks (PjFreeCommon's tfuzz_free_specO PB FX) *)
Variable PB : astate -> Prop.
Variable FX : pf_obs.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).

(* ---- the entry ---- *)
Record PfEnt : Type := MkPfEnt {
  fe_ly : alayout; fe_S : astate; fe_Hp : list Z; fe_W : world SEGS; fe_regs : bvmap 5 word;
  fe_mem : word -> option byte; fe_md : Model; fe_ch : list (Z * Z * Z);
  fe_d : Z; fe_v : Z; fe_D : list (Z * Z); fe_F : list (Z * Z); fe_Lam : list (Z * Z);
  fe_peak : Z; fe_cnt : Z; fe_fail : Z; fe_ran : Z; fe_n : nat; fe_most : Z; fe_own : Z }.
Definition fe_sp0 (en : PfEnt) : Z := spZ (fe_regs en).
Definition fe_FP (en : PfEnt) : list (Z * Z) :=
  if fe_v en =? 0 then [] else (fe_v en, fe_v en + 56) :: ablocks_fp (prhPj_hbl (fe_D en)).

(* tpj_free_specOP's premises, verbatim, over the entry record *)
Definition pf_pre (en : PfEnt) : Prop :=
  let ly := fe_ly en in let S := fe_S en in let Hp := fe_Hp en in let W := fe_W en in let regs := fe_regs en in
  let mem := fe_mem en in let md := fe_md en in let ch := fe_ch en in let d := fe_d en in let v := fe_v en in
  let D := fe_D en in let F := fe_F en in let Lam := fe_Lam en in let n := fe_n en in
  fpre (PA := PA) B ARx (STK_pj_free n) ly S Hp W regs mem md ch /\
  prh_univ_closure B CTX0 /\ room_live_cf S /\
  getr regs 10 = w64 v /\
  fwin (PA := PA) ly W regs mem d /\
  (v = 0 /\ D = [] /\ F = [] \/
   v <> 0 /\ v < YM05.alloc_ceiling /\ pj_foR SEGS (rdW W mem) (prh_lin Lam) n v D F /\
   prhPj_slot (PA := PA) B (STK_pj_free n) d ly S Lam W regs mem v) /\
  (v <> 0 -> pf_safe FX PB F ly S) /\
  prh_ledger (PA := PA) B ly S Hp W mem Lam (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en)
    (fe_own en).

(* the post body over the entry's values *)
Definition pf_Q (en : PfEnt) : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word ->
    (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
  (pf_K0post (PA := PA) B (fe_D en) (fe_v en) (fe_ly en) (fe_S en) (fe_Hp en) (fe_Lam en)
     (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en) (fe_own en) ly' S' Hp' W' regs' mem' md' /\
   pf_reach FX (fe_F en) (fe_ly en) (fe_S en) [] ly' S') /\
  (Pm (fe_mem en) -> Pm mem').

(* the walk's goal: the text's post, fpostW's R form at wle' SEGS RZ_cf *)
Definition pf_FIN (en : PfEnt) : world SEGS -> config -> Prop :=
  fpostWR (PA := PA) B ARx SK (wle' SEGS RZ_cf) (STK_pj_free (fe_n en)) (fe_d en) (fe_FP en)
    (fe_regs en) (fe_ly en) (fe_S en) (fe_Hp en) (fe_W en) (fe_mem en) (fe_md en) (pf_Q en).

(* the configuration at a cut *)
Definition pf_cfg (pc : Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : config :=
  mkCfg (mkst regs (Z_to_bv 64 (BASE + (AF_pf + pc))) mem (seg_rom SEGS)) md.

(* ---- v's node at the entry (v <> 0): its header and its block lists, pj_oshapeR's witnesses ---- *)
Record PfNode : Type := MkPfNode {
  fn_ty : Z; fn_num : Z; fn_str : Z; fn_kids : Z; fn_keys : Z; fn_n : Z; fn_cap : Z; fn_ks : bool;
  fn_Ds : list (Z * Z); fn_Dk : list (Z * Z); fn_Dy : list (Z * Z); fn_Di : list (Z * Z); fn_Fi : list (Z * Z) }.
(* the node's own blocks, freed after the loop in this order *)
Definition fn_own (nd : PfNode) : list (Z * Z) := fn_Dk nd ++ fn_Dy nd ++ fn_Ds nd.
Definition pf_node (en : PfEnt) (nd : PfNode) : Prop :=
  let m := rdW (fe_W en) (fe_mem en) in let lblk := prh_lin (fe_Lam en) in
  NoDup (fe_D en) /\ pj_apartR (fe_D en) (fe_v en) /\
  pj_hdrR SEGS m (fe_v en) (fn_ty nd) (fn_num nd) (fn_str nd) (fn_kids nd) (fn_keys nd) (fn_n nd) (fn_cap nd) /\
  (fn_str nd = 0 /\ fn_Ds nd = [] \/ exists k, lblk (fn_str nd) k /\ fn_Ds nd = [(fn_str nd, k)]) /\
  (fn_kids nd = 0 /\ fn_n nd = 0 /\ fn_Dk nd = [] \/
   exists k, lblk (fn_kids nd) k /\ 56 * fn_n nd <= k /\ fn_Dk nd = [(fn_kids nd, k)]) /\
  (fn_keys nd = 0 /\ fn_ks nd = false /\ fn_Dy nd = [] \/
   fn_ks nd = true /\ exists k, lblk (fn_keys nd) k /\ 8 * fn_n nd <= k /\ fn_Dy nd = [(fn_keys nd, k)]) /\
  Permutation (fe_D en) (fn_Ds nd ++ fn_Dk nd ++ fn_Dy nd ++ fn_Di nd) /\
  fe_F en = fn_Fi nd ++ fn_own nd /\
  match fe_n en with
  | O => fn_n nd = 0 /\ fn_Di nd = [] /\ fn_Fi nd = []
  | S d' => pf_oitemsR SEGS m lblk (pj_foR SEGS m lblk d') (fn_ks nd) (fn_kids nd) (fn_keys nd) (Z.to_nat (fn_n nd))
              (fn_Di nd) (fn_Fi nd)
  end.

(* ---- what holds at every cut after the prologue ---- *)
(* the frame: the journal from the entry at the widened window, footprint fe_FP; the caller's window outside the
   footprint untouched; sp lowered by 96; the saved ra, s0 .. s10 in their slots; the frame present; gp, tp and s11
   (which pj_free never writes) kept; the read-only view; the memory invariant *)
Definition pf_frame (en : PfEnt) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  AJ (STK_pj_free (fe_n en) + fe_d en) (fe_sp0 en + fe_d en) (fe_FP en)
    (fe_ly en) (fe_S en) (fe_Hp en) (fe_W en) (fe_mem en) (fe_md en) [] ly S Hp W mem md k /\
  (forall a, fe_sp0 en <= a < fe_sp0 en + fe_d en -> ~ inFP (fe_FP en) a ->
     aview SEGS (w_H W) mem a = aview SEGS (w_H (fe_W en)) (fe_mem en) a) /\
  spZ regs = fe_sp0 en - 96 /\
  (forall o r, In (o, r) pf_saves1 ->
     val_mem SEGS (rdW W mem) (fe_sp0 en - 96 + o) 8 (bv_unsigned (getr (fe_regs en) (Z_to_bv 5 (Z.of_nat r))))) /\
  (forall a, fe_sp0 en - 96 <= a < fe_sp0 en -> apresent (w_H W) mem a) /\
  getr regs 3 = getr (fe_regs en) 3 /\ getr regs 4 = getr (fe_regs en) 4 /\ getr regs 27 = getr (fe_regs en) 27 /\
  arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H W) mem) /\
  (Pm (fe_mem en) -> Pm mem).

(* pf_frame over a world relation R: the journal conjunct is the journal's R form (ajournal_xR, whose fourth conjunct
   is R W W'), every other conjunct as in pf_frame. pf_frame keeps its own body for pfa_frame_same (S6PjFreeGlue.v:242)
   and pfk_frame (S6PjFreeKeep.v:312), which state it; S6PjFreeEnt.v:139 unfolds pf_frameR. It is this at wle (pf_frame_R_wle) *)
Definition pf_frameR (R : world SEGS -> world SEGS -> Prop) (en : PfEnt) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  ajournal_xR (SK := SK) SEGS B PST ARx R (STK_pj_free (fe_n en) + fe_d en) (fe_sp0 en + fe_d en) (fe_FP en)
    (fe_ly en) (fe_S en) (fe_Hp en) (fe_W en) (fe_mem en) (fe_md en) [] ly S Hp W mem md k /\
  (forall a, fe_sp0 en <= a < fe_sp0 en + fe_d en -> ~ inFP (fe_FP en) a ->
     aview SEGS (w_H W) mem a = aview SEGS (w_H (fe_W en)) (fe_mem en) a) /\
  spZ regs = fe_sp0 en - 96 /\
  (forall o r, In (o, r) pf_saves1 ->
     val_mem SEGS (rdW W mem) (fe_sp0 en - 96 + o) 8 (bv_unsigned (getr (fe_regs en) (Z_to_bv 5 (Z.of_nat r))))) /\
  (forall a, fe_sp0 en - 96 <= a < fe_sp0 en -> apresent (w_H W) mem a) /\
  getr regs 3 = getr (fe_regs en) 3 /\ getr regs 4 = getr (fe_regs en) 4 /\ getr regs 27 = getr (fe_regs en) 27 /\
  arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H W) mem) /\
  (Pm (fe_mem en) -> Pm mem).

Lemma pf_frame_R_wle : forall en ly S Hp W regs mem md k,
  pf_frame en ly S Hp W regs mem md k = pf_frameR (@wle SEGS) en ly S Hp W regs mem md k.
Proof. reflexivity. Qed.

(* v's node at a state: its header words str / kids / keys / n as at the entry, its 56 bytes writable, outside the
   allocator's, below alloc_ceiling, its shadow addressable and its hull visible, and where it lives (prhReader_at's
   first three places, never one of D's blocks) *)
Definition pf_vnode (en : PfEnt) (nd : PfNode) (ly : alayout) (S : astate) (Lam : list (Z * Z)) (W : world SEGS)
  (mem : word -> option byte) : Prop :=
  let v := fe_v en in let m := rdW W mem in
  4096 <= v /\ v + 56 <= YM05.alloc_ceiling /\ v mod 8 = 0 /\ amem_range v 56 /\
  rd_u64 SEGS m (v + 16) (fn_str nd) /\ rd_u64 SEGS m (v + 24) (fn_kids nd) /\
  rd_u64 SEGS m (v + 32) (fn_keys nd) /\ rd_u64 SEGS m (v + 40) (fn_n nd) /\
  pj_rwR SEGS m v /\ (forall a, v <= a < v + 56 -> ~ aowned B ly S a) /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 56 /\ shadow_hull_vis (aview SEGS (w_H W) mem) v 56 /\
  ((exists a k, In (a, k) Lam /\ ~ In (a, k) (fe_D en) /\ a <= v /\ v + 56 <= a + k) \/
   (exists b m, In (b, m) (ablocks B ly S) /\ ~ In (b + 16, m - 16) Lam /\ b <= v /\ v + 56 <= b + m) \/
   (exists cid pos, In (cid, pos) (frames S) /\
      frame_addr ly cid pos <= v /\ v + 56 <= frame_addr ly cid pos + fs_frame_bytes cid)).

(* the registers holding v's fields (s0 = v, s1 = v+32, s2 = v+40, s3 = v+24), the shadow offset s4 and s5, the cell of
   v+40 *)
Definition pf_vregs (en : PfEnt) (regs : bvmap 5 word) : Prop :=
  let v := fe_v en in
  getr regs 8 = w64 v /\ getr regs 9 = w64 (v + 32) /\ getr regs 18 = w64 (v + 40) /\
  getr regs 19 = w64 (v + 24) /\ getr regs 20 = w64 SHADOW_OFF /\
  getr regs 21 = w64 ((v + 40) / 8 + SHADOW_OFF).
(* the loop registers at slot i: s6 = 56 i, s7 = 8 i, s8 = i, s9 = the cell of v+24, s10 = the cell of v+32 *)
Definition pf_lregs (en : PfEnt) (regs : bvmap 5 word) (i : Z) : Prop :=
  let v := fe_v en in
  getr regs 22 = w64 (56 * i) /\ getr regs 23 = w64 (8 * i) /\ getr regs 24 = w64 i /\
  getr regs 25 = w64 ((v + 24) / 8 + SHADOW_OFF) /\ getr regs 26 = w64 ((v + 32) / 8 + SHADOW_OFF).

(* the accounts at a state: the room, the ledger at Lam, the freed blocks Fd off the entry's Lam and off its allocator
   blocks, the order so far (F = Fd ++ Fr, Fd taken off F's front in order by the observed fuzz_free calls) *)
Definition pf_acct (en : PfEnt) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (mem : word -> option byte) (Fd Fr Lam : list (Z * Z)) : Prop :=
  room_live_cf S /\
  prh_ledger (PA := PA) B ly S Hp W mem Lam (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en)
    (fe_own en) /\
  Permutation (fe_Lam en) (Fd ++ Lam) /\
  Permutation (ablocks B (fe_ly en) (fe_S en)) (prhPj_hbl Fd ++ ablocks B ly S) /\
  fe_F en = Fd ++ Fr /\
  pf_reach FX (fe_F en) (fe_ly en) (fe_S en) Fr ly S.

(* ---- the cuts: the frame's journal at wle' SEGS RZ_cf (every cut but the entry's pf_LX at n = 0 and pf_LH at i = 0
   lies after a free or a recursive pj_free; the entry's journal starts at wle', ajournal_x_init_WR) ---- *)
(* LOOP HEAD at slot i of a node of depth S d': the slots i .. n-1 still to free, in the current memory and ledger *)
Definition pf_LH (en : PfEnt) (nd : PfNode) (d' : nat) (i : Z) (ly : alayout) (S : astate)
  (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  fe_n en = Datatypes.S d' /\ 0 <= i < fn_n nd /\
  pf_frameR (wle' SEGS RZ_cf) en ly S Hp W regs mem md k /\ pf_vregs en regs /\ pf_lregs en regs i /\
  exists Fd Lam Dr Fr,
    pf_acct en ly S Hp W mem Fd (Fr ++ fn_own nd) Lam /\ pf_vnode en nd ly S Lam W mem /\
    Permutation (fe_D en) (Fd ++ Dr ++ fn_own nd) /\
    pf_oitemsR SEGS (rdW W mem) (prh_lin Lam) (pj_foR SEGS (rdW W mem) (prh_lin Lam) d') (fn_ks nd)
      (fn_kids nd + 56 * i) (fn_keys nd + 8 * i) (Z.to_nat (fn_n nd - i)) Dr Fr.

(* AFTER SLOT i's SUBTREE (the recursive call's return site): its key Dk (pj_keyR at keys + 8 i) still to free, then
   the slots i + 1 .. n - 1 *)
Definition pf_LK (en : PfEnt) (nd : PfNode) (d' : nat) (i : Z) (ly : alayout) (S : astate)
  (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  fe_n en = Datatypes.S d' /\ 0 <= i < fn_n nd /\
  pf_frameR (wle' SEGS RZ_cf) en ly S Hp W regs mem md k /\ pf_vregs en regs /\ pf_lregs en regs i /\
  exists Fd Lam Dk Dr Fr,
    pf_acct en ly S Hp W mem Fd (Dk ++ Fr ++ fn_own nd) Lam /\ pf_vnode en nd ly S Lam W mem /\
    Permutation (fe_D en) (Fd ++ Dk ++ Dr ++ fn_own nd) /\
    pj_keyR SEGS (rdW W mem) (prh_lin Lam) (fn_ks nd) (fn_keys nd + 8 * i) Dk /\
    pf_oitemsR SEGS (rdW W mem) (prh_lin Lam) (pj_foR SEGS (rdW W mem) (prh_lin Lam) d') (fn_ks nd)
      (fn_kids nd + 56 * (i + 1)) (fn_keys nd + 8 * (i + 1)) (Z.to_nat (fn_n nd - (i + 1))) Dr Fr.

(* SLOT i DONE (after the key's fuzz_free, or the keys = NULL skip): the slots i + 1 .. n - 1 still to free *)
Definition pf_LC (en : PfEnt) (nd : PfNode) (d' : nat) (i : Z) (ly : alayout) (S : astate)
  (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  fe_n en = Datatypes.S d' /\ 0 <= i < fn_n nd /\
  pf_frameR (wle' SEGS RZ_cf) en ly S Hp W regs mem md k /\ pf_vregs en regs /\ pf_lregs en regs i /\
  exists Fd Lam Dr Fr,
    pf_acct en ly S Hp W mem Fd (Fr ++ fn_own nd) Lam /\ pf_vnode en nd ly S Lam W mem /\
    Permutation (fe_D en) (Fd ++ Dr ++ fn_own nd) /\
    pf_oitemsR SEGS (rdW W mem) (prh_lin Lam) (pj_foR SEGS (rdW W mem) (prh_lin Lam) d') (fn_ks nd)
      (fn_kids nd + 56 * (i + 1)) (fn_keys nd + 8 * (i + 1)) (Z.to_nat (fn_n nd - (i + 1))) Dr Fr.

(* AFTER THE LOOP: every slot freed; kids, keys, str to free *)
Definition pf_LX (en : PfEnt) (nd : PfNode) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  pf_frameR (wle' SEGS RZ_cf) en ly S Hp W regs mem md k /\ pf_vregs en regs /\
  exists Fd Lam,
    pf_acct en ly S Hp W mem Fd (fn_own nd) Lam /\ pf_vnode en nd ly S Lam W mem /\
    Permutation (fe_D en) (Fd ++ fn_own nd).

(* EPILOGUE: the post holds; the frame still to pop *)
Definition pf_EP (en : PfEnt) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  pf_frameR (wle' SEGS RZ_cf) en ly S Hp W regs mem md k /\ pf_Q en ly S Hp W regs mem md.

(* ---- the segment statements ---- *)
(* the entry: the prologue, then v = NULL to the ret, or n = 0 to the cut after the loop, or the loop head at slot 0 *)
Definition pfs_entry : Prop :=
  forall en, pf_pre en ->
  (forall nd ly S Hp W regs mem md k, pf_node en nd -> pf_LX en nd ly S Hp W regs mem md k ->
     SRr' SEGS RZ_cf W (pf_cfg PF_LX regs mem md) (pf_FIN en)) ->
  (forall nd d' ly S Hp W regs mem md k, pf_node en nd -> pf_LH en nd d' 0 ly S Hp W regs mem md k ->
     SRr' SEGS RZ_cf W (pf_cfg PF_LH regs mem md) (pf_FIN en)) ->
  SRr' SEGS RZ_cf (fe_W en) (cfg_at SEGS (SIGMA AS_pj_free) (fe_regs en) (fe_mem en) (fe_md en)) (pf_FIN en).
Definition pfs_EP : Prop :=
  forall en ly S Hp W regs mem md k, pf_pre en ->
  pf_EP en ly S Hp W regs mem md k -> SRr' SEGS RZ_cf W (pf_cfg PF_EP regs mem md) (pf_FIN en).
Definition pfs_LX : Prop :=
  forall en nd ly S Hp W regs mem md k, pf_pre en -> pf_node en nd -> fe_v en <> 0 ->
  pf_LX en nd ly S Hp W regs mem md k -> SRr' SEGS RZ_cf W (pf_cfg PF_LX regs mem md) (pf_FIN en).
(* the loop head at slot i to the recursive call's return site; d' is the children's depth, whose text the recursive
   call cites (a premise of the segment lemma, never this file's claim) *)
Definition pfs_LH (d' : nat) : Prop :=
  forall en nd i ly S Hp W regs mem md k, pf_pre en -> pf_node en nd -> fe_v en <> 0 ->
  pf_LH en nd d' i ly S Hp W regs mem md k ->
  (forall ly1 S1 Hp1 W1 regs1 mem1 md1 k1, pf_LK en nd d' i ly1 S1 Hp1 W1 regs1 mem1 md1 k1 ->
     SRr' SEGS RZ_cf W1 (pf_cfg PF_LK regs1 mem1 md1) (pf_FIN en)) ->
  SRr' SEGS RZ_cf W (pf_cfg PF_LH regs mem md) (pf_FIN en).
(* the key's free (or none: keys = NULL) *)
Definition pfs_LK (d' : nat) : Prop :=
  forall en nd i ly S Hp W regs mem md k, pf_pre en -> pf_node en nd -> fe_v en <> 0 ->
  pf_LK en nd d' i ly S Hp W regs mem md k ->
  (forall ly1 S1 Hp1 W1 regs1 mem1 md1 k1, pf_LC en nd d' i ly1 S1 Hp1 W1 regs1 mem1 md1 k1 ->
     SRr' SEGS RZ_cf W1 (pf_cfg PF_LC regs1 mem1 md1) (pf_FIN en)) ->
  SRr' SEGS RZ_cf W (pf_cfg PF_LK regs mem md) (pf_FIN en).
(* the bound test `bltu s8, a0`: to slot i + 1 or out of the loop *)
Definition pfs_LC (d' : nat) : Prop :=
  forall en nd i ly S Hp W regs mem md k, pf_pre en -> pf_node en nd -> fe_v en <> 0 ->
  pf_LC en nd d' i ly S Hp W regs mem md k ->
  (forall ly1 S1 Hp1 W1 regs1 mem1 md1 k1, pf_LH en nd d' (i + 1) ly1 S1 Hp1 W1 regs1 mem1 md1 k1 ->
     SRr' SEGS RZ_cf W1 (pf_cfg PF_LH regs1 mem1 md1) (pf_FIN en)) ->
  (forall ly1 S1 Hp1 W1 regs1 mem1 md1 k1, pf_LX en nd ly1 S1 Hp1 W1 regs1 mem1 md1 k1 ->
     SRr' SEGS RZ_cf W1 (pf_cfg PF_LX regs1 mem1 md1) (pf_FIN en)) ->
  SRr' SEGS RZ_cf W (pf_cfg PF_LC regs mem md) (pf_FIN en).
End c.

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx (@cf_head CP).
Hypothesis TL : PALib B.
(* image facts, discharged at PI_prog_A: the GOT word of the shadow base and the shadow cell lie in the image's
   segments *)
Hypothesis Hobj : forall i, 0 <= i < 8 -> in_img SEGS (VAL (A_OBJ 0) + i) /\ in_img SEGS (VAL (A_OBJ 12) + i).
Local Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).

Lemma pf_stk : forall n, STK_pj_free (PI := prh_img_A) (S n) = 96 + STK_pj_free (PI := prh_img_A) n.
Proof.
intros n. unfold STK_pj_free.
lazymatch goal with |- ?x * ?f + ?z = 96 + (?y * ?f + ?z) =>
  assert (Ef : f = 96) by (vm_compute; reflexivity); rewrite Ef; set (zz := z) end.
rewrite (Nat2Z.inj_succ (S n)). lia.
Qed.
Lemma pf_stk0 : forall n, 96 + STK_fuzz_free (PI := prh_img_A) <= STK_pj_free (PI := prh_img_A) n /\
  96 + 4096 <= STK_pj_free (PI := prh_img_A) n.
Proof.
intros n. unfold STK_pj_free.
lazymatch goal with |- _ <= ?x * ?f + ?z /\ _ =>
  assert (Ef : f = 96) by (vm_compute; reflexivity);
  let zv := eval vm_compute in z in assert (Ez : z = zv) by (vm_compute; reflexivity); rewrite Ef, Ez end.
lazymatch eval vm_compute in (STK_fuzz_free (PI := prh_img_A)) with ?fv =>
  assert (EF2 : STK_fuzz_free (PI := prh_img_A) = fv) by (vm_compute; reflexivity) end.
rewrite EF2. lia.
Qed.

(* the ordered shape of a node, uniform in the depth (pj_foR's witnesses, pf_node's fields) *)
Lemma pf_oshape : forall m lblk n p D F, pj_foR SEGS m lblk n p D F ->
  NoDup D /\ pj_apartR D p /\
  exists ty num str kids keys nn cap ks Ds Dk Dy Di Fi,
    pj_hdrR SEGS m p ty num str kids keys nn cap /\
    (str = 0 /\ Ds = [] \/ exists k, lblk str k /\ Ds = [(str, k)]) /\
    (kids = 0 /\ nn = 0 /\ Dk = [] \/ exists k, lblk kids k /\ 56 * nn <= k /\ Dk = [(kids, k)]) /\
    (keys = 0 /\ ks = false /\ Dy = [] \/ ks = true /\ exists k, lblk keys k /\ 8 * nn <= k /\ Dy = [(keys, k)]) /\
    Permutation D (Ds ++ Dk ++ Dy ++ Di) /\ F = Fi ++ Dk ++ Dy ++ Ds /\
    (n = 0%nat -> nn = 0 /\ Di = [] /\ Fi = []) /\
    (forall d', n = S d' -> pf_oitemsR SEGS m lblk (pj_foR SEGS m lblk d') ks kids keys (Z.to_nat nn) Di Fi).
Proof.
intros m lblk n p D F H. destruct n as [|d']; cbn [pj_foR] in H; unfold pj_oshapeR in H;
  destruct H as (HN & HA & ty & num & str & kids & keys & nn & cap & ks & Ds & Dk & Dy & Di & Fi & Hh & Hs & Hk & Hy & HP & HI & HF);
  (split; [exact HN|]); (split; [exact HA|]);
  exists ty, num, str, kids, keys, nn, cap, ks, Ds, Dk, Dy, Di, Fi;
  (split; [exact Hh|]); (split; [exact Hs|]); (split; [exact Hk|]); (split; [exact Hy|]); (split; [exact HP|]);
  (split; [exact HF|]).
- split; [intros _; exact HI | intros d'' E; discriminate E].
- split; [intros E; discriminate E | intros d'' E; injection E as <-; exact HI].
Qed.

(* where a node's 56 bytes lie (prhPj_slot's place without its caller-window case, p < alloc_ceiling <= the entry sp):
   each byte in a live allocator block or in a frame of the entry's frames, and off the image *)
Lemma pf_vplace : forall STK ly S Hp W regs mem md d Lam peak cnt fail ran most own v,
  ARx ly S Hp W mem md ->
  prh_ledger (cp := CP) (PI := prh_img_A) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhPj_slot (cp := CP) (PA := PA) B STK d ly S Lam W regs mem v ->
  v < YM05.alloc_ceiling -> YM05.alloc_ceiling <= spZ regs ->
  forall a, v <= a < v + 56 ->
  ((exists b n, In (b, n) (ablocks B ly S) /\ b <= a < b + req_size n) \/
   (exists cid pos, In (cid, pos) (frames S) /\ in_zr a (frame_rng ly (cid, pos)))) /\ ~ in_img SEGS a.
Proof.
intros STK ly S Hp W regs mem md d Lam peak cnt fail ran most own v HAR HLED HSL Hv Hsp a Ha.
destruct HSL as (H4096 & HAT & _).
assert (HP : (exists b n, In (b, n) (ablocks B ly S) /\ b <= a < b + req_size n) \/
   (exists cid pos, In (cid, pos) (frames S) /\ in_zr a (frame_rng ly (cid, pos)))).
{ destruct HAT as [(a0 & k0 & Hin & Ha0 & Hk0) | [(b & m & Hin & _ & Hb & Hm) | [(cid & pos & Hin & Hf & Hfm) | (Hs & _)]]].
  - left. destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a0 k0 _ _ HLED Hin) as (Hk & Hab & _).
    exists (a0 - @cf_head CP), (k0 + @cf_head CP). split; [exact Hab|].
    change (@cf_head CP) with 16 in *. pose proof (req_size_pos (k0 + 16) ltac:(lia)). lia.
  - left. exists b, m. split; [exact Hin|]. pose proof (req_size_pos m ltac:(lia)). lia.
  - right. exists cid, pos. split; [exact Hin|]. unfold in_zr, frame_rng. cbn [fst snd]. lia.
  - exfalso. lia. }
split; [exact HP|].
destruct HP as [(b & n & Hin & Hr) | (cid & pos & Hin & Hr)].
- exact (blk_img_x SEGS B ARx LAWS ly S Hp W mem md b n a HAR Hin Hr).
- unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. exact (frm_img_x SEGS B ARx LAWS ly S Hp W mem md cid pos a HAR Hin Hr).
Qed.

Lemma pf_entry : forall ly S Hp W (regs : bvmap 5 word) mem md ch dn,
  afn_pre_x SEGS B ARx (STK_pj_free (PI := prh_img_A) dn) ly S Hp W regs mem md ch ->
  st_ok_pi SEGS VAL (pf_E regs) ss_pf (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_pf)) mem (seg_rom SEGS))) /\
  sh_ok SEGS PF_Bx [] (pf_E regs) (mrestrict (w_H W) mem).
Proof.
intros ly S Hp W regs mem md ch dn HPRE. split; [|constructor].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL) in Kgot. rewrite (pal_cell B TL) in Kgot, Kcell.
pose proof (pal_got_cell B TL) as HgcD.
assert (HgL : forall i, 0 <= i < 8 -> 0 <= VAL (A_OBJ 0) + i < kLowMemEnd /\ 0 <= VAL (A_OBJ 12) + i < kLowMemEnd).
{ intros i Hi. destruct (Hobj i Hi) as [H1 H2]. split; apply (@pa_segs_low _ _ PA); assumption. }
destruct (HgL 0 ltac:(lia)) as [HgotR HcellR]. destruct (HgL 7 ltac:(lia)) as [HgotR7 HcellR7].
destruct (pf_stk0 dn) as [FS FS2].
assert (Hes : ESTACK = 4096) by reflexivity.
set (E := pf_E regs).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SHADOW_OFF]) n)
  by (intros n Hn; subst E; unfold pf_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite EL by (unfold A_TEXT; lia); change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (Eo0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; unfold pf_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; unfold pf_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 12)) as R12.
rewrite restrict_mkst_fx. unfold ss_pf. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold pf_regions, stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros a Ha. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eo0 R0). split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite Eo12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12 R12). split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 PF_Bx SHADOW_OFF);
    [cbn [sv_denot PF_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; lia | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
- apply pairwise_disjoint_of_extents. unfold pf_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eo0 R0), (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12 R12).
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hslo Hceil C1 C2 C3 C4 C5 HgotR HcellR HgotR7 HcellR7 HgcD FS FS2 Hes.
  unfold kLowMemEnd. clear. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [pf_facts f_atoms atoms_ok].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Usp; change (2 ^ 4) with 16;
    revert Hslo Hshi H47 Hceil C1 FS FS2 Hes Hstk0 Hal16; clear; intros; repeat split; lia|].
  split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
  rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.


Section g.
#[local] Existing Instance prh_img_A.
#[local] Existing Instance CfParams_preset.
Variable CTX0 : list (list Z).
Variable PB : astate -> Prop.
Variable FX : pf_obs.

(* the stack numbers at the entry *)
Lemma pf_sp : forall en, pf_pre B ARx CTX0 PB FX en ->
  2 ^ 46 <= fe_sp0 en - STK_pj_free (fe_n en) /\ fe_sp0 en <= 2 ^ 47 /\ fe_sp0 en mod 16 = 0 /\
  YM05.alloc_ceiling <= fe_sp0 en - STK_pj_free (fe_n en).
Proof.
intros en HPRE. pose proof HPRE as ([HFPRE0 _] & _).
pose proof HFPRE0 as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold fe_sp0. unfold YM05.alloc_ceiling in *. repeat split; lia.
Qed.

(* the tail's environment: the registers, then v's str / kids / keys / n *)
Definition PFT_E (regs : bvmap 5 word) (nd : PfNode) : env :=
  @Eimg _ A_prog_listing PA (Ereg regs [w64 (fn_str nd); w64 (fn_kids nd); w64 (fn_keys nd); w64 (fn_n nd)]).

(* ---- seating the tail's symbolic state at any pc, from pj_free's v registers ---- *)
Lemma pft_seat : forall en nd (W : world SEGS) regs mem pc,
  pf_vregs en regs -> 2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  4096 <= fe_v en <= 2 ^ 47 - 64 -> fe_v en mod 8 = 0 ->
  rd_u64 SEGS (mrestrict (w_H W) mem) (fe_v en + 16) (fn_str nd) ->
  rd_u64 SEGS (mrestrict (w_H W) mem) (fe_v en + 24) (fn_kids nd) ->
  rd_u64 SEGS (mrestrict (w_H W) mem) (fe_v en + 32) (fn_keys nd) ->
  rd_u64 SEGS (mrestrict (w_H W) mem) (fe_v en + 40) (fn_n nd) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (fe_v en) 56 -> amem_range (fe_v en) 56 ->
  st_ok_pi SEGS VAL (PFT_E regs nd) (ss_pft pc) (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))) /\
  sh_ok SEGS PFT_Bx PFT_SH (PFT_E regs nd) (mrestrict (w_H W) mem).
Proof.
intros en nd W regs mem pc HVR Hsp Hal Hv Hv8 Hstr Hkids Hkeys Hnn Hra Hamr.
pose proof HVR as (R8 & R9 & R18 & R19 & R20 & R21).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (v := fe_v en) in *.
set (E := PFT_E regs nd).
assert (Er : forall n0 (r : bv 5), (n0 < 32)%nat -> Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr regs r).
{ intros n0 r Hn Hr. unfold E, PFT_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n0 r Hr). }
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) =
  nth j [w64 (fn_str nd); w64 (fn_kids nd); w64 (fn_keys nd); w64 (fn_n nd)] (Z_to_bv 64 0)).
{ intros j Hj. unfold E, PFT_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ j). }
assert (U8 : forall c, 0 <= c <= 56 -> U E (SOff 8 c) = v + c).
{ intros c Hc. apply (U_atom_off E 8 v c); [rewrite (Er 8%nat 8%bv) by (first [lia | reflexivity]); exact R8 | lia | lia]. }
assert (U20 : U E (SOff 20 0) = SHADOW_OFF).
{ apply (U_atom E 20 SHADOW_OFF); [rewrite (Er 20%nat 20%bv) by (first [lia | reflexivity]); exact R20 | unfold SHADOW_OFF; lia]. }
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (Er 2%nat 2%bv) by (first [lia | reflexivity]); reflexivity).
assert (Uv : bv_unsigned (ew E 8) = v).
{ rewrite (Er 8%nat 8%bv) by (first [lia | reflexivity]). rewrite R8. apply unsigned_lit_small. lia. }
assert (DU : forall e, sv_denot E e = Z_to_bv 64 (U E e)) by (intros e; unfold U; symmetry; apply Z_to_bv_bv_unsigned).
assert (Hcell : forall c, 0 <= c <= 56 -> U E (pft_cell (SOff 8 c)) = (v + c) / 8 + SHADOW_OFF).
{ intros c Hc. unfold pft_cell. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu, U_SLit. cbn [zalu_raw].
  replace (Z.land (zcanon 3) 63) with 3 by (vm_compute; reflexivity).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite U8 by lia. rewrite U20.
  assert (Hq : 0 <= (v + c) / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia).
  unfold zcanon, M64, SHADOW_OFF in *. apply Z.mod_small. lia. }
split.
- rewrite restrict_mkst_fx. unfold ss_pft. apply pa_entry_st_ok_full.
  + rewrite pft_sregs_eq.
    apply regs_ok_pin; [|pft_regne|rewrite R21, DU, Hcell by lia; reflexivity].
    apply regs_ok_pin; [|pft_regne|rewrite R19, DU, U8 by lia; reflexivity].
    apply regs_ok_pin; [|pft_regne|rewrite R18, DU, U8 by lia; reflexivity].
    apply regs_ok_pin; [|pft_regne|rewrite R9, DU, U8 by lia; reflexivity].
    unfold E, PFT_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold region_ok, pft_vhdr.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Uv.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ _ 16 8 (SOff 32 0) (fn_str nd));
        [rewrite DU, (U_atom E 32 (fn_str nd)); [reflexivity | exact (EX 0%nat ltac:(lia)) | exact (proj1 Hstr)]
        | cbn; exact (proj1 Hstr) | cbn; lia | exact (proj2 Hstr)].
    * apply (chunk_ok_val SEGS E _ _ 24 8 (SOff 33 0) (fn_kids nd));
        [rewrite DU, (U_atom E 33 (fn_kids nd)); [reflexivity | exact (EX 1%nat ltac:(lia)) | exact (proj1 Hkids)]
        | cbn; exact (proj1 Hkids) | cbn; lia | exact (proj2 Hkids)].
    * apply (chunk_ok_val SEGS E _ _ 32 8 (SOff 34 0) (fn_keys nd));
        [rewrite DU, (U_atom E 34 (fn_keys nd)); [reflexivity | exact (EX 2%nat ltac:(lia)) | exact (proj1 Hkeys)]
        | cbn; exact (proj1 Hkeys) | cbn; lia | exact (proj2 Hkeys)].
    * apply (chunk_ok_val SEGS E _ _ 40 8 (SOff 35 0) (fn_n nd));
        [rewrite DU, (U_atom E 35 (fn_n nd)); [reflexivity | exact (EX 3%nat ltac:(lia)) | exact (proj1 Hnn)]
        | cbn; exact (proj1 Hnn) | cbn; lia | exact (proj2 Hnn)].
  + cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  + split; [|split; [exact I | exact I]].
    unfold pft_facts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, Uv. rewrite (Er 20%nat 20%bv) by (first [lia | reflexivity]). rewrite R20. unfold w64.
    rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; try exact Hal; try exact Hv8; try lia.
- unfold sh_ok, PFT_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E PFT_Bx 8 v 56 v 0 56 Hra).
  + unfold PFT_Bx. exact U20.
  + rewrite U8 by lia. lia.
  + lia. + lia.
  + intros x Hx. unfold amem_range in Hamr. unfold SHADOW_OFF in *. lia.
Qed.
End g.
End f.
End d.
