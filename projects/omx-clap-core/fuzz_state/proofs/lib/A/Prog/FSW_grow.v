(* The ASan walk of grow (fs.asan 0x83a48, pf.c:42-63) against FSH_Fn_reader.grow_spec: the STAGES. rule 24: grow is proved
   new (a Theorem Labs lane's lookup, CONFIRM 06:14Z: no released branch holds an omx-clap-core proof of grow); the released PLAIN
   walk (lib/Prog/grow_c.v) is the control-flow template; (internal path) section 4
   is the measured shape (released walk plus eight inline shadow checks; no fake frame; one auipc, the shadow-base GOT
   word).

   PROVED STAGES (each a CPS lemma: the run from a stated symbolic state to its next stop, the stop's facts handed on):
     grow_stageA  entry 0x83a48 (FSW_K.fsw_entryT_argsX, v's region at atom 10) .. n < cap: the ret 0x83b98;
                  n = cap: entering fuzz_realloc (kids) from 0x83af4, with 1 <= 56 * cap' and 1 <= 8 * cap' proved.
     grow_stageB  resume at 0x83af8 (FSW_ret fss_retT) .. type 6: entering fuzz_realloc (keys) from 0x83b44;
                  other types: the ret, after the kids store 0x83b08 and the cap store 0x83b64.
     grow_stageC  resume at 0x83b48 .. the ret, after the keys store 0x83b54 and the cap store 0x83b64.
   Every inline check is shown not taken: in stage A as token obligations from v's range_addressable, after a call
   as shent-covered loads (the shadow base is then s7, atom 23), and the three checks through SAVED shadow addresses
   (0x83b00 s8, 0x83b4c s7, 0x83b58 s5) by FSW_shcell's 1-byte zero shadow-cell regions. No __asan_report_* is reached.
   The stores carry awr_byte premises on exactly v's written fields (v + 0x18, + 0x20, + 0x30): grow_spec's FP
   [(v + 24, v + 40); (v + 48, v + 56)] covers only those bytes of v.

   THE COMPOSITION grow_holds : grow_spec is FSW_grow_holds.v: the n < cap arm through FSW_ret.fsw_retU (v off the image by
   FSW_rd.fsw_pobj_off_img), the n = cap arm through the two fuzz_realloc calls (FSW_K3.fsw_after_callFPU_args over
   ALLOC's fuzz_realloc_spec, a named Section hypothesis there). This file keeps grow_FP and grow_post, the footprint and
   the post of grow_spec, for it.
   Named premise everywhere: FsShadowSyms B (FSH_Base.v), the shadow-base cells; TfibLib B discharges it. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSW_K FSW_ret FSPstat FSH_Fn_reader FSW_rd FSW_pj.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require ReaderRes PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YN1e.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog Require Import FSW_grow_tbl FSW_shcell.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ---- stage A's symbolic entry state: FSW_K's fss0T_args with v as FSW_pj's read-only object region at atom 10. Extra
   atoms by FSW_K's convention (xatom i = 33 + i, the i-th entry of xs): the alloc.c statics first (xatom 0..3 = cnt,
   fail, live, peak, the order of the ALLOC kit's fs_extraTS), then v's fields in FSW_pj.pj_fields order (xatom 4..8 =
   ty, kids, keys, n, cap: atoms 37..41). ---- *)
Definition grow_xs (cnt fail live peak ty kids keys n cap : Z) : list word :=
  map (Z_to_bv 64) [cnt; fail; live; peak] ++ pj_fields ty kids keys n cap.
Definition grow_objA : YP09.region := pj_obj_regionRX 10 4.
(* v: a struct pj (56 bytes, 8-aligned) of the application memory below alloc_ceiling; its type a u32 *)
Definition grow_gfA : list (nat * afact) := pj_obj_factsX 10 4 4096 (0x7fffff800000 - 56) 0 (2 ^ 32 - 1).
Definition ss_gA0 : sstate := Eval vm_compute in fss0T_args A_grow 80 [grow_objA] grow_gfA.

(* the frame grow's prologue writes (0x83a4c-0x83a70): ra, s0 .. s8 at entry sp - 8 .. entry sp - 80 *)
Definition grow_saved : list (Z * bv 5) :=
  [(-8, 1%bv); (-16, 8%bv); (-24, 9%bv); (-32, 18%bv); (-40, 19%bv); (-48, 20%bv); (-56, 21%bv); (-64, 22%bv);
   (-72, 23%bv); (-80, 24%bv)].
Definition grow_frame (m : word -> option byte) (sp : Z) (regs0 : bvmap 5 word) : Prop :=
  Forall (fun p => val_mem tfibsegs m (sp + fst p) 8 (bv_unsigned (YK11.getr regs0 (snd p)))) grow_saved.

(* what stage A establishes at the call of fuzz_realloc (kids) 0x83af4 (n = cap, cap' = ReaderRes.cap2 cap): the
   argument registers, ALLOC's size premise 1 <= n for both of grow's calls, every register the walk reads after the
   call, and the frame *)
Definition grow_call_kids (W : world tfibsegs) (regs regsC : bvmap 5 word) (memC : word -> option byte)
  (v cap kids : Z) : Prop :=
  YK11.getr regsC 1 = w64 0x83af8 /\ spZ regsC = spZ regs - 80 /\
  YK11.getr regsC 10 = w64 kids /\ YK11.getr regsC 11 = w64 (56 * ReaderRes.cap2 cap) /\
  1 <= 56 * ReaderRes.cap2 cap /\ 1 <= 8 * ReaderRes.cap2 cap /\
  YK11.getr regsC 8 = w64 (v + 48) /\ YK11.getr regsC 9 = w64 v /\
  YK11.getr regsC 19 = w64 (8 * ReaderRes.cap2 cap) /\ YK11.getr regsC 20 = w64 (v + 24) /\
  YK11.getr regsC 21 = w64 (SHADOW_OFF + (v + 48) / 8) /\ YK11.getr regsC 22 = w64 (ReaderRes.cap2 cap) /\
  YK11.getr regsC 23 = w64 SHADOW_OFF /\ YK11.getr regsC 24 = w64 (SHADOW_OFF + (v + 24) / 8) /\
  Forall (fun r => YK11.getr regsC r = YK11.getr regs r) [3; 4; 18; 25; 26; 27]%bv /\
  grow_frame (mrestrict (w_H W) memC) (spZ regs) regs.

(* a register of the stopped run, as the symbolic state says: getr (ms_regs ms) r is the denotation of the run's sv for r *)
Ltac gw_reg HS r :=
  rewrite (st_ok_restrict_reg tfibsegs _ _ _ _ r HS);
  lazymatch goal with |- sv_denot _ (sr_get ?l ?q) = _ =>
    let e := eval vm_compute in (sr_get l q) in change (sr_get l q) with e end.
(* ... equal to w64 X: by its unsigned value *)
Ltac gw_val :=
  apply bv_eq; unfold w64; rewrite unsigned_lit_small by (unfold SHADOW_OFF in *; lia);
  lazymatch goal with |- bv_unsigned (sv_denot ?E ?e) = _ => change (bv_unsigned (sv_denot E e)) with (YP0e.U E e) end.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the shadow-base cells of B (FSH_Base.FsShadowSyms, S0 5478e5af284), the one named premise of fs's instrumented walks;
   TfibLib B (A/ACeg.v) discharges it once A/ACej.v builds *)
Hypothesis HSS : FsShadowSyms B.

Lemma grow_stageA : forall ly S U (W : world tfibsegs) regs mem md ch (FP : list (Z * Z)) v ty num str kids keys n cap
  (cnt fail live peak : Z) (Q : world tfibsegs -> config -> Prop),
  afn_preU tfibsegs B STK_grow ly S U W regs mem md ch ->
  YK11.getr regs 10 = w64 v ->
  4096 <= v -> v + 56 <= alloc_ceiling -> (v + 56 <= 0x10000 \/ FS_IMG_END <= v) ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF v 56 ->
  PjStruct.pj_hdr tfibsegs (mrestrict (w_H W) mem) v ty num str kids keys n cap ->
  0 <= n <= cap -> cap <= 2 ^ 54 ->
  (* n < cap: at the ret 0x83b98 *)
  (n < cap -> forall E' ssf msf mat,
     st_ok tfibsegs E' ssf (restrict (w_H W) msf) -> ss_resv ssf = None ->
     clookup grow_tbl (ss_pc ssf) = Some RET_WORD_r ->
     YK11.getr (ms_regs msf) 1 = YK11.getr regs 1 -> YK11.getr (ms_regs msf) 10 = w64 0 ->
     aregs_preserved regs (ms_regs msf) ->
     ajournal tfibsegs B STK_grow (spZ regs) FP ly S W (unpoison U mem) md [] ly S W (unpoison U (ms_mem msf))
       (with_vm_backing (m_vm_lazy md) mat md) 0 ->
     ARU tfibsegs B ly S U W (ms_mem msf) (with_vm_backing (m_vm_lazy md) mat md) ->
     same_below mem (ms_mem msf) alloc_ceiling ->
     SRr tfibsegs W (mkCfg msf (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  (* n = cap: entering fuzz_realloc from 0x83af4 *)
  (n = cap -> forall regsC memC mat,
     grow_call_kids W regs regsC memC v cap kids ->
     ajournal tfibsegs B STK_grow (spZ regs) FP ly S W (unpoison U mem) md [] ly S W (unpoison U memC)
       (with_vm_backing (m_vm_lazy md) mat md) 0 ->
     ARU tfibsegs B ly S U W memC (with_vm_backing (m_vm_lazy md) mat md) ->
     same_below mem memC alloc_ceiling ->
     SRr tfibsegs W (YG0d.cfg_at tfibsegs A_fuzz_realloc regsC memC (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_grow regs mem md) Q.
Proof.
intros ly S U W regs mem md ch FP v ty num str kids keys n cap cnt fail live peak Q HPRE H10 Hv4 Hvc Hvimg Hra HHDR Hn Hc KLT KEQ.
pose proof HHDR as ((Hv8 & _) & (Hty & _) & _ & _ & (Hk & _) & (Hkeys & _) & _ & _).
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fs_segs_low as HSL. pose proof fs_wx as HWX.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof (fsw_sp B _ ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof HPRE as (HAP & HUOK & HUP).
pose proof HAP as (_ & Hra1 & _).
assert (FS : STK_grow = ltac:(let x := eval vm_compute in STK_grow in exact x)) by reflexivity.
(* ---- the entry state: fsw_entryT_argsX with v's region and fact ---- *)
set (xs := grow_xs cnt fail live peak ty kids keys n cap).
set (E1 := Ereg regs (fs_extraT ++ xs)).
assert (ER : forall r : bv 5, (Z.to_nat (bv_unsigned r) < 32)%nat -> ew E1 (Z.to_nat (bv_unsigned r)) = YK11.getr regs r)
  by (intros r _; subst E1; apply ew_Ereg_reg).
assert (E10 : bv_unsigned (ew E1 10) = v).
{ subst E1. rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl). change (YK11.getr regs 10) with (getr regs 10) in H10.
  rewrite H10. unfold w64. apply wz. lia. }
assert (EX : forall j, ew E1 (32 + j) = nth j (fs_extraT ++ xs) (Z_to_bv 64 0)) by (intros j; subst E1; apply ew_Ereg_extra).
assert (E32 : ew E1 32 = Z_to_bv 64 SHADOW_OFF) by (change 32%nat with (32 + 0)%nat; rewrite EX; reflexivity).
(* v's fields at xatom 4..8 (FSW_K's convention, FSW_pj.pj_fields order): n at atom 40, cap at 41, kids at 38 *)
assert (XW : firstn 5 (skipn 4 xs) = pj_fields ty kids keys n cap) by reflexivity.
assert (E33 : ew E1 40 = Z_to_bv 64 n) by (change 40%nat with (32 + 8)%nat; rewrite EX; reflexivity).
assert (E34 : ew E1 41 = Z_to_bv 64 cap) by (change 41%nat with (32 + 9)%nat; rewrite EX; reflexivity).
assert (E35 : ew E1 38 = Z_to_bv 64 kids) by (change 38%nat with (32 + 6)%nat; rewrite EX; reflexivity).
assert (E2 : bv_unsigned (ew E1 2) = spZ regs) by (subst E1; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (Ev : ew E1 10 = Z_to_bv 64 v) by (subst E1; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (HS3 : st_ok tfibsegs E1 ss_gA0 (restrict (w_H W) (mkst regs (Z_to_bv 64 A_grow) mem (seg_rom tfibsegs)))).
{ change ss_gA0 with (fss0T_args A_grow 80 [grow_objA] grow_gfA).
  apply (fsw_entryT_argsX B STK_grow 80 ly S U W regs mem md ch A_grow [grow_objA] grow_gfA xs
    (proj1 HSS) (proj2 HSS) HPRE ltac:(rewrite FS; lia) ltac:(vm_compute; reflexivity)).
  - constructor; [|constructor]. exact (fsw_pj_obj_regionRX_ok tfibsegs regs xs 4 _ 10 v ty num str kids keys n cap HHDR Ev XW).
  - assert (STK_grow >= 80) by (rewrite FS; lia).
    apply (fsw_pj_obj_disjWX regs _ 80 10 0 0 _ _ _ _ _ v Ev); [lia | lia | lia | left; lia | |];
      unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, FS_IMG_END in *; lia.
  - apply (fsw_pj_obj_factsX_ok tfibsegs regs xs 4 _ 10 4096 (0x7fffff800000 - 56) 0 (2 ^ 32 - 1) v ty num str kids keys n cap
      HHDR Ev XW); lia. }
unfold YG0d.cfg_at. change (w64 A_grow) with (Z_to_bv 64 A_grow).
pose proof (ajournal_init tfibsegs B STK_grow FP ly S W regs (unpoison U mem) md ch HAP) as HJ.
pose proof (fsw_ARU B STK_grow ly S U W regs mem md ch HPRE) as HARU.
assert (SHOK : sh_ok tfibsegs fs_Bx [] E1 (mrestrict (w_H W) mem)) by apply Forall_nil.
change mem with (ms_mem (mkst regs (Z_to_bv 64 A_grow) mem (seg_rom tfibsegs))) in HJ at 2, HARU, SHOK.
assert (U32 : YP0e.U E1 fs_Bx = SHADOW_OFF).
{ unfold fs_Bx. rewrite U_SOff, E32, Z.add_0_r, unsigned_lit_small by (unfold SHADOW_OFF; lia).
  apply zcanon_small. unfold SHADOW_OFF; lia. }
assert (UV : forall c, 0 <= c <= 56 -> YP0e.U E1 (SOff 10 c) = v + c).
{ intros c Hc0. rewrite U_SOff, E10. apply zcanon_small. lia. }
(* ---- 0x83a48 .. 0x83ab4: prologue, shadow base, the checks of v + 0x28 and v + 0x30 ---- *)
fsw_aj_run_tokU grow_tbl_ok HS3 HJ HARU SHOK fs_Bspan.
1,2: cbn [ms_mem mkst]; rewrite U32, UV by lia; apply (range_addressable_sub _ _ v 56); [exact Hra | lia | lia].
{ awr_ok_tac. exact E2. }
assert (SB1 : same_below mem (ms_mem ms) alloc_ceiling).
{ intros x Hx. apply HF. intros (r & Hin & Hr). cbn [ss_gA0 ss_mem In] in Hin.
  repeat (destruct Hin as [<-|Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; try lia|]); [|destruct Hin].
  rewrite E2, unsigned_lit_small in Hr by lia. lia. }
clear HF HFr HG.
lazymatch type of HS3 with st_ok _ ?E _ _ => set (E2' := E) in * end.
assert (EA : forall k, (k < 42)%nat -> ew E2' k = ew E1 k) by (intros kk Hkk; subst E2'; rewrite !ew_ewset_other by lia; reflexivity).
assert (U2v : forall c, 0 <= c <= 56 -> YP0e.U E2' (SOff 10 c) = v + c) by (intros c Hc0; rewrite U_SOff, EA by lia; rewrite <- U_SOff; apply UV; exact Hc0).
assert (U2B : YP0e.U E2' fs_Bx = SHADOW_OFF) by (unfold fs_Bx; rewrite U_SOff, EA by lia; rewrite <- U_SOff; exact U32).
assert (U2n : YP0e.U E2' (SOff 40 0) = n) by (apply U_atom; [rewrite EA by lia; exact E33 | lia]).
assert (U2c : YP0e.U E2' (SOff 41 0) = cap) by (apply U_atom; [rewrite EA by lia; exact E34 | lia]).
assert (U2k : YP0e.U E2' (SOff 38 0) = kids) by (apply U_atom; [rewrite EA by lia; exact E35 | lia]).
assert (E22 : bv_unsigned (ew E2' 2) = spZ regs) by (rewrite EA by lia; exact E2).
assert (ER2 : forall r : bv 5, (Z.to_nat (bv_unsigned r) < 32)%nat -> ew E2' (Z.to_nat (bv_unsigned r)) = YK11.getr regs r)
  by (intros r Hr; rewrite EA by lia; exact (ER r Hr)).
(* ---- 0x83ab4 bgeu n, cap ---- *)
eapply SRr_sym_branch with (c := BC_GEU) (a := SOff 40 0) (b := SOff 41 0); [exact HS3 | |].
- intros Hb HS4. clear HS3. rewrite branch_geu_U, U2n, U2c in Hb. apply negb_true_iff, Z.ltb_ge in Hb.
  assert (Hnc : n = cap) by lia. clear Hb.
  assert (SHOK2 : sh_ok tfibsegs fs_Bx [] E2' (mrestrict (w_H W) (ms_mem ms))) by apply Forall_nil.
  (* ---- 0x83ac0 bnez cap ---- *)
  fsw_aj_run_tokU grow_tbl_ok HS4 HJ HARU SHOK2 fs_Bspan.
  { awr_ok_tac. exact E22. }
  assert (SB2 : same_below mem (ms_mem ms0) alloc_ceiling).
  { apply (same_below_trans _ (ms_mem ms)); [exact SB1|]. intros x Hx. apply HF. intros (r & Hin & Hr).
    cbn [ss_mem add_cond In] in Hin.
    repeat (destruct Hin as [<-|Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; try lia|]); [|destruct Hin].
    rewrite E22, unsigned_lit_small in Hr by lia. lia. }
  clear HF HFr HG SB1.
  assert (Hra2 : range_addressable (aview tfibsegs (w_H W) (ms_mem ms0)) SHADOW_OFF v 56).
  { intros x Hx. destruct (Hra x Hx) as (s & Hs1 & Hs2). exists s. split; [|exact Hs2].
    rewrite (aview_below (w_H W) mem (ms_mem ms0) alloc_ceiling); [exact Hs1 | exact SB2|].
    unfold shadow_of_addr, SHADOW_OFF. lia. }
  eapply SRr_sym_branch with (c := BC_NE) (a := SOff 41 0) (b := SLit 0); [exact HS4 | |].
  + intros Hb2 HS5. clear HS4. rewrite branch_ne_U, U2c, U_lit in Hb2 by lia. apply negb_true_iff, Z.eqb_neq in Hb2.
    assert (SHOK3 : sh_ok tfibsegs fs_Bx [] E2' (mrestrict (w_H W) (ms_mem ms0))) by apply Forall_nil.
    fsw_aj_run_to_tokU grow_tbl_ok HS5 HJ HARU SHOK3 fs_Bspan A_fuzz_realloc.
    { rewrite U2B, U2v by lia. apply (range_addressable_sub _ _ v 56); [exact Hra2 | lia | lia]. }
    { awr_ok_tac. exact E22. }
    lazymatch type of HS5 with st_ok _ ?E _ _ => set (E3 := E) in * end.
    assert (EA3 : forall k, (k < 42)%nat -> ew E3 k = ew E1 k) by (intros kk Hkk; subst E3; rewrite ew_ewset_other by lia; apply EA; exact Hkk).
    assert (U3v : forall c, 0 <= c <= 56 -> YP0e.U E3 (SOff 10 c) = v + c) by (intros c Hc0; rewrite U_SOff, EA3 by lia; rewrite <- U_SOff; apply UV; exact Hc0).
    assert (U3B : YP0e.U E3 (SOff 32 0) = SHADOW_OFF) by (rewrite U_SOff, EA3 by lia; rewrite <- U_SOff; exact U32).
    assert (U3c : YP0e.U E3 (SOff 41 0) = cap) by (apply U_atom; [rewrite EA3 by lia; exact E34 | lia]).
    assert (U3k : YP0e.U E3 (SOff 38 0) = kids) by (apply U_atom; [rewrite EA3 by lia; exact E35 | lia]).
    assert (E32b : bv_unsigned (ew E3 2) = spZ regs) by (rewrite EA3 by lia; exact E2).
    assert (ER3 : forall r : bv 5, (Z.to_nat (bv_unsigned r) < 32)%nat -> ew E3 (Z.to_nat (bv_unsigned r)) = YK11.getr regs r)
      by (intros r Hr; rewrite EA3 by lia; exact (ER r Hr)).
    assert (SB3 : same_below mem (ms_mem ms1) alloc_ceiling).
    { apply (same_below_trans _ (ms_mem ms0)); [exact SB2|]. intros x Hx. apply HF. intros (r & Hin & Hr).
      cbn [ss_mem add_cond In] in Hin.
      repeat (destruct Hin as [<-|Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; try lia|]); [|destruct Hin].
      rewrite E22, unsigned_lit_small in Hr by lia. lia. }
    pose proof (fsw_region_nth _ _ _ 0 _ HS5 eq_refl) as HR1. cbn [ms_mem restrict] in HR1.
    assert (Hcap2 : 1 <= ReaderRes.cap2 cap /\ ReaderRes.cap2 cap <= 2 ^ 55) by (unfold ReaderRes.cap2; destruct (Z.eqb_spec cap 0); lia).
    rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms1 HS5 eq_refl).
    apply (KEQ Hnc (ms_regs ms1) (ms_mem ms1) mat1); [| exact HJ | exact HARU | exact SB3].
    unfold grow_call_kids.
    split; [gw_reg HS5 (1%bv : bv 5); gw_val; apply U_lit; lia|].
    split; [unfold spZ at 1; rewrite (fsw_reg_off _ _ _ ms1 2%bv 2 (-80) (spZ regs) HS5 ltac:(vm_compute; reflexivity) E32b ltac:(lia)); lia|].
    split; [gw_reg HS5 (10%bv : bv 5); gw_val; exact U3k|].
    split; [gw_reg HS5 (11%bv : bv 5); gw_val; rewrite U_SMd; cbn [zmd_raw]; rewrite U3c, U_lit by lia; unfold ReaderRes.cap2; rewrite (proj2 (Z.eqb_neq cap 0) Hb2); rewrite zcanon_small by lia; lia|].
    split; [lia|]. split; [lia|].
    split; [gw_reg HS5 (8%bv : bv 5); gw_val; apply U3v; lia|].
    split; [gw_reg HS5 (9%bv : bv 5); gw_val; rewrite U3v by lia; lia|].
    split; [gw_reg HS5 (19%bv : bv 5); gw_val; rewrite U_SAlu; cbn [zalu_raw]; rewrite U3c, U_lit by lia; change (Z.land 4 63) with 4; rewrite Z.shiftl_mul_pow2 by lia; unfold ReaderRes.cap2; rewrite (proj2 (Z.eqb_neq cap 0) Hb2); rewrite zcanon_small by lia; lia|].
    split; [gw_reg HS5 (20%bv : bv 5); gw_val; apply U3v; lia|].
    split; [gw_reg HS5 (21%bv : bv 5); gw_val; rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SAlu; cbn [zalu_raw]; rewrite U3v, U_lit, U3B by lia;
      change (Z.land 3 63) with 3; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8;
      rewrite (zcanon_small ((v + 48) / 8)) by (pose proof (Z.div_pos (v + 48) 8); pose proof (Z.div_le_upper_bound (v + 48) 8 (2 ^ 60)); lia);
      rewrite zcanon_small by (pose proof (Z.div_pos (v + 48) 8); pose proof (Z.div_le_upper_bound (v + 48) 8 (2 ^ 60)); unfold SHADOW_OFF; lia); lia|].
    split; [gw_reg HS5 (22%bv : bv 5); gw_val; rewrite U_SAlu; cbn [zalu_raw]; rewrite U3c, U_lit by lia; change (Z.land 1 63) with 1; rewrite Z.shiftl_mul_pow2 by lia; unfold ReaderRes.cap2; rewrite (proj2 (Z.eqb_neq cap 0) Hb2); rewrite zcanon_small by lia; lia|].
    split; [gw_reg HS5 (23%bv : bv 5); gw_val; exact U3B|].
    split; [gw_reg HS5 (24%bv : bv 5); gw_val; rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SAlu; cbn [zalu_raw]; rewrite U3v, U_lit, U3B by lia;
      change (Z.land 3 63) with 3; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8;
      rewrite (zcanon_small ((v + 24) / 8)) by (pose proof (Z.div_pos (v + 24) 8); pose proof (Z.div_le_upper_bound (v + 24) 8 (2 ^ 60)); lia);
      rewrite zcanon_small by (pose proof (Z.div_pos (v + 24) 8); pose proof (Z.div_le_upper_bound (v + 24) 8 (2 ^ 60)); unfold SHADOW_OFF; lia); lia|].
    split.
    { repeat (apply Forall_cons; [lazymatch goal with |- YK11.getr _ ?r = _ => gw_reg HS5 r; rewrite fsw_SOff0; exact (ER3 r ltac:(vm_compute; lia)) end|]). apply Forall_nil. }
    unfold grow_frame, grow_saved.
    repeat (apply Forall_cons; [cbn [fst snd];
      lazymatch goal with |- val_mem _ _ (_ + ?o) 8 (bv_unsigned (YK11.getr regs ?r)) =>
        apply (fsw_field _ _ 2 _ _ _ _ _ _ o 8%N (SOff (Z.to_nat (bv_unsigned r)) 0) _ HR1 E32b ltac:(cbn; tauto));
        [rewrite fsw_SOff0, ER3 by (vm_compute; lia); symmetry; apply Z_to_bv_bv_unsigned | apply u64_range | cbn; lia] end|]).
    apply Forall_nil.
  + intros Hb2 HS5. clear HS4. rewrite branch_ne_U, U2c, U_lit in Hb2 by lia. apply negb_false_iff, Z.eqb_eq in Hb2.
    assert (SHOK3 : sh_ok tfibsegs fs_Bx [] E2' (mrestrict (w_H W) (ms_mem ms0))) by apply Forall_nil.
    fsw_aj_run_to_tokU grow_tbl_ok HS5 HJ HARU SHOK3 fs_Bspan A_fuzz_realloc.
    { rewrite U2B, U2v by lia. apply (range_addressable_sub _ _ v 56); [exact Hra2 | lia | lia]. }
    { awr_ok_tac. exact E22. }
    lazymatch type of HS5 with st_ok _ ?E _ _ => set (E3 := E) in * end.
    assert (EA3 : forall k, (k < 42)%nat -> ew E3 k = ew E1 k) by (intros kk Hkk; subst E3; rewrite ew_ewset_other by lia; apply EA; exact Hkk).
    assert (U3v : forall c, 0 <= c <= 56 -> YP0e.U E3 (SOff 10 c) = v + c) by (intros c Hc0; rewrite U_SOff, EA3 by lia; rewrite <- U_SOff; apply UV; exact Hc0).
    assert (U3B : YP0e.U E3 (SOff 32 0) = SHADOW_OFF) by (rewrite U_SOff, EA3 by lia; rewrite <- U_SOff; exact U32).
    assert (U3c : YP0e.U E3 (SOff 41 0) = cap) by (apply U_atom; [rewrite EA3 by lia; exact E34 | lia]).
    assert (U3k : YP0e.U E3 (SOff 38 0) = kids) by (apply U_atom; [rewrite EA3 by lia; exact E35 | lia]).
    assert (E32b : bv_unsigned (ew E3 2) = spZ regs) by (rewrite EA3 by lia; exact E2).
    assert (ER3 : forall r : bv 5, (Z.to_nat (bv_unsigned r) < 32)%nat -> ew E3 (Z.to_nat (bv_unsigned r)) = YK11.getr regs r)
      by (intros r Hr; rewrite EA3 by lia; exact (ER r Hr)).
    assert (SB3 : same_below mem (ms_mem ms1) alloc_ceiling).
    { apply (same_below_trans _ (ms_mem ms0)); [exact SB2|]. intros x Hx. apply HF. intros (r & Hin & Hr).
      cbn [ss_mem add_cond In] in Hin.
      repeat (destruct Hin as [<-|Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; try lia|]); [|destruct Hin].
      rewrite E22, unsigned_lit_small in Hr by lia. lia. }
    pose proof (fsw_region_nth _ _ _ 0 _ HS5 eq_refl) as HR1. cbn [ms_mem restrict] in HR1.
    assert (Hcap2 : 1 <= ReaderRes.cap2 cap /\ ReaderRes.cap2 cap <= 2 ^ 55) by (unfold ReaderRes.cap2; destruct (Z.eqb_spec cap 0); lia).
    rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms1 HS5 eq_refl).
    apply (KEQ Hnc (ms_regs ms1) (ms_mem ms1) mat1); [| exact HJ | exact HARU | exact SB3].
    unfold grow_call_kids.
    split; [gw_reg HS5 (1%bv : bv 5); gw_val; apply U_lit; lia|].
    split; [unfold spZ at 1; rewrite (fsw_reg_off _ _ _ ms1 2%bv 2 (-80) (spZ regs) HS5 ltac:(vm_compute; reflexivity) E32b ltac:(lia)); lia|].
    split; [gw_reg HS5 (10%bv : bv 5); gw_val; exact U3k|].
    split; [gw_reg HS5 (11%bv : bv 5); gw_val; rewrite U_lit by lia; unfold ReaderRes.cap2; rewrite Hb2; reflexivity|].
    split; [lia|]. split; [lia|].
    split; [gw_reg HS5 (8%bv : bv 5); gw_val; apply U3v; lia|].
    split; [gw_reg HS5 (9%bv : bv 5); gw_val; rewrite U3v by lia; lia|].
    split; [gw_reg HS5 (19%bv : bv 5); gw_val; rewrite U_lit by lia; unfold ReaderRes.cap2; rewrite Hb2; reflexivity|].
    split; [gw_reg HS5 (20%bv : bv 5); gw_val; apply U3v; lia|].
    split; [gw_reg HS5 (21%bv : bv 5); gw_val; rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SAlu; cbn [zalu_raw]; rewrite U3v, U_lit, U3B by lia;
      change (Z.land 3 63) with 3; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8;
      rewrite (zcanon_small ((v + 48) / 8)) by (pose proof (Z.div_pos (v + 48) 8); pose proof (Z.div_le_upper_bound (v + 48) 8 (2 ^ 60)); lia);
      rewrite zcanon_small by (pose proof (Z.div_pos (v + 48) 8); pose proof (Z.div_le_upper_bound (v + 48) 8 (2 ^ 60)); unfold SHADOW_OFF; lia); lia|].
    split; [gw_reg HS5 (22%bv : bv 5); gw_val; rewrite U_lit by lia; unfold ReaderRes.cap2; rewrite Hb2; reflexivity|].
    split; [gw_reg HS5 (23%bv : bv 5); gw_val; exact U3B|].
    split; [gw_reg HS5 (24%bv : bv 5); gw_val; rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SAlu; cbn [zalu_raw]; rewrite U3v, U_lit, U3B by lia;
      change (Z.land 3 63) with 3; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8;
      rewrite (zcanon_small ((v + 24) / 8)) by (pose proof (Z.div_pos (v + 24) 8); pose proof (Z.div_le_upper_bound (v + 24) 8 (2 ^ 60)); lia);
      rewrite zcanon_small by (pose proof (Z.div_pos (v + 24) 8); pose proof (Z.div_le_upper_bound (v + 24) 8 (2 ^ 60)); unfold SHADOW_OFF; lia); lia|].
    split.
    { repeat (apply Forall_cons; [lazymatch goal with |- YK11.getr _ ?r = _ => gw_reg HS5 r; rewrite fsw_SOff0; exact (ER3 r ltac:(vm_compute; lia)) end|]). apply Forall_nil. }
    unfold grow_frame, grow_saved.
    repeat (apply Forall_cons; [cbn [fst snd];
      lazymatch goal with |- val_mem _ _ (_ + ?o) 8 (bv_unsigned (YK11.getr regs ?r)) =>
        apply (fsw_field _ _ 2 _ _ _ _ _ _ o 8%N (SOff (Z.to_nat (bv_unsigned r)) 0) _ HR1 E32b ltac:(cbn; tauto));
        [rewrite fsw_SOff0, ER3 by (vm_compute; lia); symmetry; apply Z_to_bv_bv_unsigned | apply u64_range | cbn; lia] end|]).
    apply Forall_nil.
- intros Hb HS4. clear HS3. rewrite branch_geu_U, U2n, U2c in Hb. apply negb_false_iff, Z.ltb_lt in Hb.
  (* ---- 0x83ab8 .. 0x83b98: s2 = 0, the epilogue, at the ret ---- *)
  fsw_aj_runU grow_tbl_ok HS4 HJ HARU.
  { awr_ok_tac. exact E22. }
  assert (SB2 : same_below mem (ms_mem ms0) alloc_ceiling).
  { apply (same_below_trans _ (ms_mem ms)); [exact SB1|]. intros x Hx. apply HF. intros (r & Hin & Hr).
    cbn [ss_mem add_cond In] in Hin.
    repeat (destruct Hin as [<-|Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; try lia|]); [|destruct Hin].
    rewrite E22, unsigned_lit_small in Hr by lia. lia. }
  apply (KLT Hb E2' _ ms0 mat0 HS4 eq_refl ltac:(vm_compute; reflexivity)); [| | | exact HJ | exact HARU | exact SB2].
  + gw_reg HS4 (1%bv : bv 5). rewrite fsw_SOff0. exact (ER2 1%bv ltac:(vm_compute; lia)).
  + gw_reg HS4 (10%bv : bv 5). gw_val. apply U_lit. lia.
  + apply (fsw_preserved (w_H W) E2' _ ms0 regs (fun r => SOff (Z.to_nat (bv_unsigned r)) 0) HS4 ltac:(vm_compute; reflexivity)).
    intros r _. rewrite fsw_SOff0. apply ER2. pose proof (u5_range r). lia.
Qed.
(* ================= grow_spec's footprint and post, for FSW_grow_holds.v's composition ================= *)
Definition grow_FP (v ty kids keys cap : Z) : list (Z * Z) :=
  [(v + 24, v + 40); (v + 48, v + 56)] ++
  ablocks_fp (rd_hblocks (ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk ty keys cap)) ++ FS_PSTAT_FP.
(* grow_spec's post, as FSH_Fn_reader.v states it (FSW_grow_holds.grow_holds checks the two agree by conversion) *)
Definition grow_post (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (v ty num str kids keys n cap live peak cnt fail : Z)
  : world tfibsegs -> config -> Prop :=
  fun W' c' => exists k' y' cap' Dold Dnew U',
    grow_res ty n cap kids keys k' y' cap' Dold Dnew U U' /\
    @fpostU fx rc SK tfibsegs B STK_grow (spZ regs) (grow_FP v ty kids keys cap) regs ly S U W mem md (rd_ev (grow_tr ty n cap)) U'
      (fun ly' S' W' regs' mem' md' =>
         YK11.getr regs' 10 = w64 0 /\
         Permutation (ablocks B ly' S' ++ rd_hblocks Dold) (ablocks B ly S ++ rd_hblocks Dnew) /\
         PjStruct.pj_hdr tfibsegs (mrestrict (w_H W') mem') v ty num str k' y' n cap' /\
         PjStruct.pj_slots_at (fun a k => In (a, k) (ReaderRes.kids_blk k' cap' ++ ReaderRes.keys_blk ty y' cap'))
           ty k' y' n cap' /\
         rd_blocks_ok tfibsegs B ly' S' W' mem' (ReaderRes.kids_blk k' cap' ++ ReaderRes.keys_blk ty y' cap') /\
         rd_moved tfibsegs W W' mem mem' kids k' (56 * cap) /\ (ty = 6 -> rd_moved tfibsegs W W' mem mem' keys y' (8 * cap)) /\
         pobj tfibsegs B ly' S' W' mem' v /\
         (exists peak', peak <= peak' /\
            fs_glob tfibsegs W' mem' (live + PjGrammar.held (grow_tr ty n cap)) peak'
              (cnt + Z.of_nat (length (grow_tr ty n cap))) fail)) W' c'.

End W.

(* ================= STAGE B: after fuzz_realloc (kids) returns to 0x83af8, to fuzz_realloc (keys) or the ret =================
   The resume state is FSW_ret's fss_retT at 0x83af8 (frame 80, the saved registers as chunks), the shape the after-call
   step (a Theorem Labs lane's fsw_after_callFPU_args) gives, with these extra regions: v's type word (atom 9 = s1 = v, [0, 4)),
   v's kids / keys slots ([24, 40), the kids slot writable), v's cap slot (atom 8 = s0 = v + 48, writable), and the two
   shadow cells grow reads through saved registers (FSW_shcell: atom 24 = s8 = the shadow of v + 24, atom 21 = s5 = the
   shadow of v + 48). Extra atoms by FSW_K's convention: statics xatom 0..3, v's type and keys xatom 4, 5, the saved ra,
   s0 .. s8 xatom 6 .. 15. The shadow base after the call is s7 (atom 23, Bx), the inline checks on v are covered by two
   shents (v's 56 bytes at atom 9, the cap slot at atom 8). The two stores the stage runs (0x83b08 v + 0x18, 0x83b64
   v + 0x30) are justified by awr_byte premises: a heap v gets them from the core today (FP inside a live block); a v in
   check_round_trip's class-3 frame gets them from the core's fourth awr_byte arm (H2, RELOC). *)
Definition grow_saved_regs : list (bv 5) := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24]%bv.
Definition grow_xsB (cnt fail live peak ty keys : Z) (regs : bvmap 5 word) : list word :=
  map (Z_to_bv 64) [cnt; fail; live; peak; ty; keys] ++ map (YK11.getr regs) grow_saved_regs.
Definition gB_cs : list YP09.chunk :=
  [YP09.mkChunk 72 (CVal 8 (SOff (xatom 6) 0)); YP09.mkChunk 64 (CVal 8 (SOff (xatom 7) 0));
   YP09.mkChunk 56 (CVal 8 (SOff (xatom 8) 0)); YP09.mkChunk 48 (CVal 8 (SOff (xatom 9) 0));
   YP09.mkChunk 40 (CVal 8 (SOff (xatom 10) 0)); YP09.mkChunk 32 (CVal 8 (SOff (xatom 11) 0));
   YP09.mkChunk 24 (CVal 8 (SOff (xatom 12) 0)); YP09.mkChunk 16 (CVal 8 (SOff (xatom 13) 0));
   YP09.mkChunk 8 (CVal 8 (SOff (xatom 14) 0)); YP09.mkChunk 0 (CVal 8 (SOff (xatom 15) 0))].
Definition gB_objT : YP09.region := YP09.mkRegion (Some 9%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff (xatom 4) 0))].
Definition gB_objK : YP09.region := YP09.mkRegion (Some 9%nat) 24 40 24 32 [YP09.mkChunk 32 (CVal 8 (SOff (xatom 5) 0))].
Definition gB_objC : YP09.region := YP09.mkRegion (Some 8%nat) 0 8 0 8 [].
Definition gB_rs : list YP09.region := [gB_objT; gB_objK; gB_objC; fs_shcell_region 24; fs_shcell_region 21].
Definition gB_gf : list (nat * afact) :=
  [(9%nat, mkAF 4096 (0x7fffff800000 - 56) 3); (8%nat, mkAF (4096 + 48) (0x7fffff800000 - 8) 3);
   (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (10%nat, mkAF (4096 + HEAD) (2 ^ 47) 4)].
Definition gB_SH : list shent := [mkSHE 9 0 56; mkSHE 8 0 8].
Definition gB_Bx : sv := SOff 23 0.
Definition ss_gB0 : sstate := Eval vm_compute in fss_retT 0x83af8 80 gB_cs gB_rs gB_gf.

(* what stage B establishes on entering fuzz_realloc (keys, 8 * cap') from 0x83b44 *)
Definition grow_call_keys (W : world tfibsegs) (regs regsR regsC : bvmap 5 word) (memC : word -> option byte)
  (v keys : Z) : Prop :=
  YK11.getr regsC 1 = w64 0x83b48 /\ spZ regsC = spZ regsR /\
  YK11.getr regsC 10 = w64 keys /\ YK11.getr regsC 11 = YK11.getr regsR 19 /\
  YK11.getr regsC 9 = w64 (v + 32) /\ YK11.getr regsC 18 = w64 (2 ^ 64 - 1) /\
  YK11.getr regsC 23 = w64 (SHADOW_OFF + (v + 32) / 8) /\
  Forall (fun r => YK11.getr regsC r = YK11.getr regsR r) [3; 4; 8; 19; 20; 21; 22; 24; 25; 26; 27]%bv /\
  grow_frame (mrestrict (w_H W) memC) (spZ regsR + 80) regs.

(* the write windows of a stage-B state: the frame, v's kids slot (atom 9), v's cap slot (atom 8) *)
Ltac gB_awr v E2 ER H9 H8 HW1 HW2 :=
  lazymatch goal with |- awr_ok ?sg ?bb ?E ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb E rs' a1 a2 a3 a4 a5 a6 a7 a8) end;
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := - 80); [reflexivity | rewrite E2; lia | cbn; lia | cbn; lia |];
  apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|];
  eapply awr_ok_cons_gen with (k := 9%nat) (b := v); [reflexivity | rewrite (ER 9%bv), H9; apply wz; lia | |];
  [cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply HW1; lia|];
  eapply awr_ok_cons_gen with (k := 8%nat) (b := v + 48); [reflexivity | rewrite (ER 8%bv), H8; apply wz; lia | |];
  [cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply HW2; lia|];
  apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil.
(* memory below alloc_ceiling outside v's two windows is kept by a stage-B run (its windows: the frame, above
   alloc_ceiling, and v's two slots) *)
Ltac gB_frame v HF E2 ER H9 H8 Hstk :=
  intros x Hx Hx1 Hx2; apply HF; intros (r & Hin & Hr);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
  repeat (destruct Hin as [<-|Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?unsigned_lit_small in Hr by lia;
    first [ lia | rewrite E2 in Hr; lia | rewrite (ER 9%bv), H9, wz in Hr by lia; lia
          | rewrite (ER 8%bv), H8, wz in Hr by lia; lia ] |]); destruct Hin.
(* sp, the saved registers of the frame, or a kept atom: the value fsw_preserved asks of each callee-saved register *)
Definition gB_expect (r : bv 5) : sv :=
  match bv_unsigned r with
  | 2 => SOff 2 80 | 8 => SOff 40 0 | 9 => SOff 41 0 | 18 => SOff 42 0 | 19 => SOff 43 0 | 20 => SOff 44 0
  | 21 => SOff 45 0 | 22 => SOff 46 0 | 23 => SOff 47 0 | 24 => SOff 48 0 | z => SOff (Z.to_nat z) 0 end.

Section WB. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

Lemma grow_stageB : forall ly S W0 mem0 md0 own lyc Sc Uc (W : world tfibsegs) regs regsR memR mdR (STK sp0 : Z)
  (FP : list (Z * Z)) k v k' cap' cnt fail live peak ty keys (Q : world tfibsegs -> config -> Prop),
  st_ok tfibsegs (Ereg regsR (fs_extraT ++ grow_xsB cnt fail live peak ty keys regs)) ss_gB0
    (restrict (w_H W) (mkst regsR (Z_to_bv 64 0x83af8) memR (seg_rom tfibsegs))) ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison Uc memR) mdR k ->
  ARU tfibsegs B lyc Sc Uc W memR mdR ->
  spZ regsR = sp0 - 80 -> sp0 = spZ regs -> 80 <= STK ->
  YK11.getr regsR 9 = w64 v -> YK11.getr regsR 8 = w64 (v + 48) -> YK11.getr regsR 10 = w64 k' ->
  YK11.getr regsR 22 = w64 cap' -> YK11.getr regsR 23 = w64 SHADOW_OFF ->
  Forall (fun r => YK11.getr regsR r = YK11.getr regs r) [3; 4; 25; 26; 27]%bv ->
  4096 <= v -> v + 56 <= alloc_ceiling -> v mod 8 = 0 ->
  0 <= k' < 2 ^ 64 -> 0 <= cap' < 2 ^ 64 -> 0 <= ty < 2 ^ 31 -> 0 <= keys < 2 ^ 64 ->
  range_addressable (aview tfibsegs (w_H W) memR) SHADOW_OFF v 56 ->
  (forall a, v <= a < v + 56 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) ->
  (forall a, v + 24 <= a < v + 32 -> awr_byte tfibsegs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (frames S) a) ->
  (forall a, v + 48 <= a < v + 56 -> awr_byte tfibsegs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (frames S) a) ->
  (* type 6 (an object): entering fuzz_realloc (keys) from 0x83b44 *)
  (ty = 6 -> forall regsC memC mat,
     grow_call_keys W regs regsR regsC memC v keys ->
     (forall x, 0 <= x < alloc_ceiling -> ~ (v + 24 <= x < v + 32) -> ~ (v + 48 <= x < v + 56) ->
        memC (Z_to_bv 64 x) = memR (Z_to_bv 64 x)) ->
     mem_grows (mrestrict (w_H W) memR) (mrestrict (w_H W) memC) ->
     val_mem tfibsegs (mrestrict (w_H W) memC) (v + 24) 8 k' ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison Uc memC) (with_vm_backing (m_vm_lazy mdR) mat mdR) k ->
     ARU tfibsegs B lyc Sc Uc W memC (with_vm_backing (m_vm_lazy mdR) mat mdR) ->
     SRr tfibsegs W (YG0d.cfg_at tfibsegs A_fuzz_realloc regsC memC (with_vm_backing (m_vm_lazy mdR) mat mdR)) Q) ->
  (* any other type: at the ret 0x83b98 *)
  (ty <> 6 -> forall E' ssf msf mat,
     st_ok tfibsegs E' ssf (restrict (w_H W) msf) -> ss_resv ssf = None ->
     clookup grow_tbl (ss_pc ssf) = Some RET_WORD_r ->
     YK11.getr (ms_regs msf) 1 = YK11.getr regs 1 -> YK11.getr (ms_regs msf) 10 = w64 0 ->
     aregs_preserved regs (ms_regs msf) ->
     (forall x, 0 <= x < alloc_ceiling -> ~ (v + 24 <= x < v + 32) -> ~ (v + 48 <= x < v + 56) ->
        ms_mem msf (Z_to_bv 64 x) = memR (Z_to_bv 64 x)) ->
     mem_grows (mrestrict (w_H W) memR) (mrestrict (w_H W) (ms_mem msf)) ->
     val_mem tfibsegs (mrestrict (w_H W) (ms_mem msf)) (v + 24) 8 k' ->
     val_mem tfibsegs (mrestrict (w_H W) (ms_mem msf)) (v + 48) 8 cap' ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison Uc (ms_mem msf))
       (with_vm_backing (m_vm_lazy mdR) mat mdR) k ->
     ARU tfibsegs B lyc Sc Uc W (ms_mem msf) (with_vm_backing (m_vm_lazy mdR) mat mdR) ->
     SRr tfibsegs W (mkCfg msf (with_vm_backing (m_vm_lazy mdR) mat mdR)) Q) ->
  SRr tfibsegs W (mkCfg (mkst regsR (Z_to_bv 64 0x83af8) memR (seg_rom tfibsegs)) mdR) Q.
Proof.
intros ly S W0 mem0 md0 own lyc Sc Uc W regs regsR memR mdR STK sp0 FP k v k' cap' cnt fail live peak ty keys Q
  HS HJ HARU Hsp Hsp0 HSTK H9 H8 H10 H22 H23 Hkeep Hv4 Hvc Hv8 Hk' Hc' Hty Hkeys Hra Happ HW1 HW2 KT6 KN6.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fs_segs_low as HSL. pose proof fs_wx as HWX.
pose proof asan_consts as (C1 & _ & C3 & _).
set (E := Ereg regsR (fs_extraT ++ grow_xsB cnt fail live peak ty keys regs)) in *.
assert (ER : forall r : bv 5, ew E (Z.to_nat (bv_unsigned r)) = YK11.getr regsR r) by (intros r; subst E; apply ew_Ereg_reg).
assert (UR : forall (r : bv 5) z c, YK11.getr regsR r = w64 z -> 0 <= z < 2 ^ 64 -> 0 <= z + c < 2 ^ 64 ->
  YP0e.U E (SOff (Z.to_nat (bv_unsigned r)) c) = z + c).
{ intros r z c Hr Hz Hzc. apply U_atom_off; [|exact Hz|exact Hzc]. rewrite ER. exact Hr. }
assert (EX : forall j, ew E (32 + j) = nth j (fs_extraT ++ grow_xsB cnt fail live peak ty keys regs) (Z_to_bv 64 0))
  by (intros j; subst E; apply ew_Ereg_extra).
assert (E2 : bv_unsigned (ew E 2) = sp0 - 80) by (rewrite (ER 2%bv); exact Hsp).
assert (U9 : forall c, 0 <= c <= 56 -> YP0e.U E (SOff 9 c) = v + c) by (intros c Hc; apply (UR 9%bv v c H9); lia).
assert (U8 : YP0e.U E (SOff 8 0) = v + 48) by (pose proof (UR 8%bv (v + 48) 0 H8 ltac:(lia) ltac:(lia)) as X; rewrite Z.add_0_r in X; exact X).
assert (UB : YP0e.U E gB_Bx = SHADOW_OFF) by (pose proof (UR 23%bv SHADOW_OFF 0 H23 ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)) as X; rewrite Z.add_0_r in X; exact X).
assert (SHOK : sh_ok tfibsegs gB_Bx gB_SH E (mrestrict (w_H W) memR)).
{ constructor; [|constructor; [|constructor]].
  - apply (shent_ok_of_range tfibsegs (w_H W) memR E gB_Bx 9 v 56 v 0 56 Hra UB); [rewrite U9 by lia; lia | lia | lia |].
    intros x Hx. apply Happ. lia.
  - apply (shent_ok_of_range tfibsegs (w_H W) memR E gB_Bx 8 v 56 (v + 48) 0 8 Hra UB U8); [lia | lia |].
    intros x Hx. apply Happ. lia. }
change memR with (ms_mem (mkst regsR (Z_to_bv 64 0x83af8) memR (seg_rom tfibsegs))) in HJ, HARU, SHOK.
(* ---- 0x83af8 .. 0x83b24: a0 <> 0, the kids check through s8, kids store, the type check, lw type ---- *)
fsw_aj_run_tokU grow_tbl_ok HS HJ HARU SHOK fs_Bspan.
{ unfold ss_gB0, fsT_ret_regions, gB_rs, gB_objT, gB_objK, gB_objC, fs_shcell_region, fstk_ret, fs_got_region, fs_bcell_region.
  cbn [ss_mem app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := - 80); [reflexivity | rewrite E2; lia | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (k := 9%nat) (b := v); [reflexivity | rewrite (ER 9%bv), H9; apply wz; lia | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply HW1. lia. }
  eapply awr_ok_cons_gen with (k := 8%nat) (b := v + 48); [reflexivity | rewrite (ER 8%bv), H8; apply wz; lia | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply HW2. lia. }
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & _).
assert (FR1 : forall x, 0 <= x < alloc_ceiling -> ~ (v + 24 <= x < v + 32) -> ~ (v + 48 <= x < v + 56) ->
  ms_mem ms (Z_to_bv 64 x) = memR (Z_to_bv 64 x)) by (gB_frame v HF E2 ER H9 H8 Hstk).
clear HF HFr. rename HG into HG1.
assert (UT : YP0e.U E (SExt true 32 (SOff 37 0)) = ty).
{ change (YP0e.U E (SExt true 32 (SOff 37 0))) with (bv_unsigned (sv_denot E (SExt true 32 (SOff 37 0)))).
  rewrite YN1e.U_sext32'. change (bv_unsigned (sv_denot E (SOff 37 0))) with (YP0e.U E (SOff 37 0)).
  rewrite (U_atom E 37 ty) by (first [change 37%nat with (32 + 5)%nat; rewrite EX; reflexivity | lia]).
  unfold YO0a.sx32. cbv zeta. rewrite Z.mod_small by lia. destruct (Z.ltb_spec ty (2 ^ 31)); lia. }
(* ---- 0x83b24 bne type, 6 ---- *)
eapply SRr_sym_branch with (c := BC_NE) (a := SExt true 32 (SOff 37 0)) (b := SLit 6); [exact HS | |].
- (* ---- type <> 6: 0x83b58 .. 0x83b98, the cap check through s5, s2 = 0, the cap store, the epilogue ---- *)
  intros Hb HS2. clear HS. rewrite branch_ne_U, UT, U_lit in Hb by lia. apply negb_true_iff, Z.eqb_neq in Hb.
  fsw_aj_run_tokU grow_tbl_ok HS2 HJ HARU SHOK fs_Bspan.
  { gB_awr v E2 ER H9 H8 HW1 HW2. }
  assert (FR2 : forall x, 0 <= x < alloc_ceiling -> ~ (v + 24 <= x < v + 32) -> ~ (v + 48 <= x < v + 56) ->
    ms_mem ms0 (Z_to_bv 64 x) = ms_mem ms (Z_to_bv 64 x)) by (gB_frame v HF E2 ER H9 H8 Hstk).
  pose proof (fsw_region_nth _ _ _ 4 _ HS2 eq_refl) as HRK. pose proof (fsw_region_nth _ _ _ 5 _ HS2 eq_refl) as HRC.
  cbn [ms_mem restrict] in HRK, HRC.
  apply (KN6 Hb E _ ms0 mat0 HS2 eq_refl ltac:(vm_compute; reflexivity)).
  + gw_reg HS2 (1%bv : bv 5). rewrite fsw_SOff0. change 39%nat with (32 + 7)%nat. rewrite EX. reflexivity.
  + gw_reg HS2 (10%bv : bv 5). gw_val. apply U_lit. lia.
  + apply (fsw_preserved (w_H W) E _ ms0 regs gB_expect HS2 ltac:(vm_compute; reflexivity)).
    intros r Hr. cbv [CALLEE_SAVED In] in Hr. repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
    lazymatch goal with |- sv_denot _ (gB_expect ?q) = _ =>
      let e := eval vm_compute in (gB_expect q) in change (gB_expect q) with e end;
    first
    [ lazymatch goal with |- sv_denot _ (SOff 2 80) = _ =>
        apply bv_eq; rewrite denot_SOff, E2, Hsp0; unfold spZ; replace (bv_unsigned (getr regs 2) - 80 + 80) with (bv_unsigned (getr regs 2)) by lia;
        apply zcanon_id; unfold M64; apply u64_range end
    | lazymatch goal with |- sv_denot _ (SOff ?q 0) = _ =>
        let j := eval vm_compute in (q - 32)%nat in change q with (32 + j)%nat end;
      rewrite fsw_SOff0, EX; reflexivity
    | rewrite fsw_SOff0;
      lazymatch goal with |- ew _ ?q = _ regs ?r =>
        change q with (Z.to_nat (bv_unsigned r)); rewrite ER;
        rewrite Forall_forall in Hkeep; apply Hkeep; cbn [In]; repeat (first [left; reflexivity | right]) end ].
  + intros x Hx Hx1 Hx2. rewrite (FR2 x Hx Hx1 Hx2). exact (FR1 x Hx Hx1 Hx2).
  + apply (mem_grows_trans _ (mrestrict (w_H W) (ms_mem ms))); assumption.
  + apply (fsw_field _ _ 9 _ _ _ _ _ _ 24 8%N (SOff 10 0) k' HRK ltac:(rewrite (ER 9%bv), H9; apply wz; lia)
      ltac:(cbn; tauto)); [rewrite fsw_SOff0, (ER 10%bv); exact H10 | cbn; lia | cbn; lia].
  + replace (v + 48) with (v + 48 + 0) by lia.
    apply (fsw_field _ _ 8 _ _ _ _ _ _ 0 8%N (SOff 22 0) cap' HRC ltac:(rewrite (ER 8%bv), H8; apply wz; lia)
      ltac:(cbn; tauto)); [rewrite fsw_SOff0, (ER 22%bv); exact H22 | cbn; lia | cbn; lia].
  + exact HJ.
  + exact HARU.
- (* ---- type 6: 0x83b28 .. 0x83b44, the keys check, ld keys, jal fuzz_realloc ---- *)
  intros Hb HS2. clear HS. rewrite branch_ne_U, UT, U_lit in Hb by lia. apply negb_false_iff, Z.eqb_eq in Hb.
  fsw_aj_run_to_tokU grow_tbl_ok HS2 HJ HARU SHOK fs_Bspan A_fuzz_realloc.
  { gB_awr v E2 ER H9 H8 HW1 HW2. }
  assert (FR2 : forall x, 0 <= x < alloc_ceiling -> ~ (v + 24 <= x < v + 32) -> ~ (v + 48 <= x < v + 56) ->
    ms_mem ms0 (Z_to_bv 64 x) = ms_mem ms (Z_to_bv 64 x)) by (gB_frame v HF E2 ER H9 H8 Hstk).
  pose proof (fsw_region_nth _ _ _ 0 _ HS2 eq_refl) as HR0. pose proof (fsw_region_nth _ _ _ 4 _ HS2 eq_refl) as HRK.
  cbn [ms_mem restrict] in HR0, HRK.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms0 HS2 eq_refl).
  apply (KT6 Hb (ms_regs ms0) (ms_mem ms0) mat0); [| | | | exact HJ | exact HARU].
  + unfold grow_call_keys.
    split; [gw_reg HS2 (1%bv : bv 5); gw_val; apply U_lit; lia|].
    split; [unfold spZ; f_equal; gw_reg HS2 (2%bv : bv 5); rewrite fsw_SOff0; exact (ER 2%bv)|].
    split; [gw_reg HS2 (10%bv : bv 5); rewrite fsw_SOff0; change 38%nat with (32 + 6)%nat; rewrite EX; reflexivity|].
    split; [gw_reg HS2 (11%bv : bv 5); rewrite fsw_SOff0; exact (ER 19%bv)|].
    split; [gw_reg HS2 (9%bv : bv 5); gw_val; apply U9; lia|].
    split; [gw_reg HS2 (18%bv : bv 5); gw_val; apply U_lit; lia|].
    split; [gw_reg HS2 (23%bv : bv 5); gw_val; rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SAlu; cbn [zalu_raw];
      rewrite U9, U_lit by lia; change (YP0e.U E (SOff 23 0)) with (YP0e.U E gB_Bx); rewrite UB;
      change (Z.land 3 63) with 3; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8;
      rewrite (zcanon_small ((v + 32) / 8)) by (pose proof (Z.div_pos (v + 32) 8); pose proof (Z.div_le_upper_bound (v + 32) 8 (2 ^ 60)); lia);
      rewrite zcanon_small by (pose proof (Z.div_pos (v + 32) 8); pose proof (Z.div_le_upper_bound (v + 32) 8 (2 ^ 60)); unfold SHADOW_OFF; lia); lia|].
    split.
    { repeat (apply Forall_cons; [lazymatch goal with |- YK11.getr _ ?r = _ => gw_reg HS2 r; rewrite fsw_SOff0; exact (ER r) end|]).
      apply Forall_nil. }
    unfold grow_frame, grow_saved.
    repeat (apply Forall_cons; [cbn [fst snd];
      lazymatch goal with |- val_mem _ _ (_ + ?o) 8 (bv_unsigned (_ regs ?r)) =>
        let o' := eval vm_compute in (80 + o) in
        replace (spZ regsR + 80 + o) with (spZ regsR + o') by lia;
        let q := eval vm_compute in (Z.to_nat (39 + (72 - o') / 8)) in
        apply (fsw_field _ _ 2 _ _ _ _ _ _ o' 8%N (SOff q 0) _ HR0 ltac:(exact (f_equal bv_unsigned (ER 2%bv))) ltac:(cbn; tauto));
        [rewrite fsw_SOff0; let j := eval vm_compute in (q - 32)%nat in change q with (32 + j)%nat; rewrite EX;
         symmetry; apply Z_to_bv_bv_unsigned | apply u64_range | cbn; lia] end|]).
    apply Forall_nil.
  + intros x Hx Hx1 Hx2. rewrite (FR2 x Hx Hx1 Hx2). exact (FR1 x Hx Hx1 Hx2).
  + apply (mem_grows_trans _ (mrestrict (w_H W) (ms_mem ms))); assumption.
  + apply (fsw_field _ _ 9 _ _ _ _ _ _ 24 8%N (SOff 10 0) k' HRK ltac:(rewrite (ER 9%bv), H9; apply wz; lia)
      ltac:(cbn; tauto)); [rewrite fsw_SOff0, (ER 10%bv); exact H10 | cbn; lia | cbn; lia].
Qed.
End WB.

(* ================= STAGE C: after fuzz_realloc (keys) returns to 0x83b48, to the ret =================
   The resume state is fss_retT at 0x83b48 with stage B's frame chunks and extra atoms (grow_xsB), and: v's keys slot
   (atom 9 = s1 = v + 32 since 0x83b28, writable), v's cap slot (atom 8 = s0 = v + 48, writable), and the two shadow
   cells read through saved registers (FSW_shcell: atom 23 = s7 = the shadow of v + 32 since 0x83b30, atom 21 = s5 = the
   shadow of v + 48). No inline check computes its address in this stage, so the run is a plain one. The two stores
   (0x83b54 v + 0x20, 0x83b64 v + 0x30) are justified by awr_byte premises, as in stage B. *)
Definition gC_objK : YP09.region := YP09.mkRegion (Some 9%nat) 0 8 0 8 [].
Definition gC_rs : list YP09.region := [gC_objK; gB_objC; fs_shcell_region 23; fs_shcell_region 21].
Definition gC_gf : list (nat * afact) :=
  [(9%nat, mkAF (4096 + 32) (0x7fffff800000 - 24) 3); (8%nat, mkAF (4096 + 48) (0x7fffff800000 - 8) 3);
   (10%nat, mkAF (4096 + HEAD) (2 ^ 47) 4)].
Definition ss_gC0 : sstate := Eval vm_compute in fss_retT 0x83b48 80 gB_cs gC_rs gC_gf.
(* the write windows of a stage-C state: the frame, v's keys slot (atom 9), v's cap slot (atom 8) *)
Ltac gC_awr v E2 ER H9 H8 HW1 HW2 :=
  lazymatch goal with |- awr_ok ?sg ?bb ?E ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb E rs' a1 a2 a3 a4 a5 a6 a7 a8) end;
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := - 80); [reflexivity | rewrite E2; lia | cbn; lia | cbn; lia |];
  apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|];
  eapply awr_ok_cons_gen with (k := 9%nat) (b := v + 32); [reflexivity | rewrite (ER 9%bv), H9; apply wz; lia | |];
  [cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply HW1; lia|];
  eapply awr_ok_cons_gen with (k := 8%nat) (b := v + 48); [reflexivity | rewrite (ER 8%bv), H8; apply wz; lia | |];
  [cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply HW2; lia|];
  apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil.

Section WC. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

Lemma grow_stageC : forall ly S W0 mem0 md0 own lyc Sc Uc (W : world tfibsegs) regs regsR memR mdR (STK sp0 : Z)
  (FP : list (Z * Z)) k v y' cap' cnt fail live peak ty keys (Q : world tfibsegs -> config -> Prop),
  st_ok tfibsegs (Ereg regsR (fs_extraT ++ grow_xsB cnt fail live peak ty keys regs)) ss_gC0
    (restrict (w_H W) (mkst regsR (Z_to_bv 64 0x83b48) memR (seg_rom tfibsegs))) ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison Uc memR) mdR k ->
  ARU tfibsegs B lyc Sc Uc W memR mdR ->
  spZ regsR = sp0 - 80 -> sp0 = spZ regs -> 80 <= STK ->
  YK11.getr regsR 9 = w64 (v + 32) -> YK11.getr regsR 8 = w64 (v + 48) -> YK11.getr regsR 10 = w64 y' ->
  YK11.getr regsR 22 = w64 cap' ->
  Forall (fun r => YK11.getr regsR r = YK11.getr regs r) [3; 4; 25; 26; 27]%bv ->
  4096 <= v -> v + 56 <= alloc_ceiling -> v mod 8 = 0 -> 0 <= y' < 2 ^ 64 -> 0 <= cap' < 2 ^ 64 ->
  (forall a, v + 32 <= a < v + 40 -> awr_byte tfibsegs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (frames S) a) ->
  (forall a, v + 48 <= a < v + 56 -> awr_byte tfibsegs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (frames S) a) ->
  (forall E' ssf msf mat,
     st_ok tfibsegs E' ssf (restrict (w_H W) msf) -> ss_resv ssf = None ->
     clookup grow_tbl (ss_pc ssf) = Some RET_WORD_r ->
     YK11.getr (ms_regs msf) 1 = YK11.getr regs 1 -> YK11.getr (ms_regs msf) 10 = w64 0 ->
     aregs_preserved regs (ms_regs msf) ->
     (forall x, 0 <= x < alloc_ceiling -> ~ (v + 32 <= x < v + 40) -> ~ (v + 48 <= x < v + 56) ->
        ms_mem msf (Z_to_bv 64 x) = memR (Z_to_bv 64 x)) ->
     mem_grows (mrestrict (w_H W) memR) (mrestrict (w_H W) (ms_mem msf)) ->
     val_mem tfibsegs (mrestrict (w_H W) (ms_mem msf)) (v + 32) 8 y' ->
     val_mem tfibsegs (mrestrict (w_H W) (ms_mem msf)) (v + 48) 8 cap' ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison Uc (ms_mem msf))
       (with_vm_backing (m_vm_lazy mdR) mat mdR) k ->
     ARU tfibsegs B lyc Sc Uc W (ms_mem msf) (with_vm_backing (m_vm_lazy mdR) mat mdR) ->
     SRr tfibsegs W (mkCfg msf (with_vm_backing (m_vm_lazy mdR) mat mdR)) Q) ->
  SRr tfibsegs W (mkCfg (mkst regsR (Z_to_bv 64 0x83b48) memR (seg_rom tfibsegs)) mdR) Q.
Proof.
intros ly S W0 mem0 md0 own lyc Sc Uc W regs regsR memR mdR STK sp0 FP k v y' cap' cnt fail live peak ty keys Q
  HS HJ HARU Hsp Hsp0 HSTK H9 H8 H10 H22 Hkeep Hv4 Hvc Hv8 Hy' Hc' HW1 HW2 KRET.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fs_segs_low as HSL. pose proof fs_wx as HWX.
pose proof asan_consts as (C1 & _ & C3 & _).
set (E := Ereg regsR (fs_extraT ++ grow_xsB cnt fail live peak ty keys regs)) in *.
assert (ER : forall r : bv 5, ew E (Z.to_nat (bv_unsigned r)) = YK11.getr regsR r) by (intros r; subst E; apply ew_Ereg_reg).
assert (EX : forall j, ew E (32 + j) = nth j (fs_extraT ++ grow_xsB cnt fail live peak ty keys regs) (Z_to_bv 64 0))
  by (intros j; subst E; apply ew_Ereg_extra).
assert (E2 : bv_unsigned (ew E 2) = sp0 - 80) by (rewrite (ER 2%bv); exact Hsp).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & _).
change memR with (ms_mem (mkst regsR (Z_to_bv 64 0x83b48) memR (seg_rom tfibsegs))) in HJ, HARU.
(* ---- 0x83b48 .. 0x83b98: a0 <> 0, the keys check through s7, the keys store, the cap check through s5, s2 = 0,
   the cap store, the epilogue ---- *)
fsw_aj_runU grow_tbl_ok HS HJ HARU.
{ gC_awr v E2 ER H9 H8 HW1 HW2. }
assert (FR : forall x, 0 <= x < alloc_ceiling -> ~ (v + 32 <= x < v + 40) -> ~ (v + 48 <= x < v + 56) ->
  ms_mem ms (Z_to_bv 64 x) = memR (Z_to_bv 64 x)).
{ intros x Hx Hx1 Hx2. apply HF. intros (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  repeat (destruct Hin as [<-|Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?unsigned_lit_small in Hr by lia;
    first [ lia | rewrite E2 in Hr; lia | rewrite (ER 9%bv), H9, wz in Hr by lia; lia
          | rewrite (ER 8%bv), H8, wz in Hr by lia; lia ] |]); destruct Hin. }
pose proof (fsw_region_nth _ _ _ 3 _ HS eq_refl) as HRK. pose proof (fsw_region_nth _ _ _ 4 _ HS eq_refl) as HRC.
cbn [ms_mem restrict] in HRK, HRC.
apply (KRET E _ ms mat HS eq_refl ltac:(vm_compute; reflexivity)).
- gw_reg HS (1%bv : bv 5). rewrite fsw_SOff0. change 39%nat with (32 + 7)%nat. rewrite EX. reflexivity.
- gw_reg HS (10%bv : bv 5). gw_val. apply U_lit. lia.
- apply (fsw_preserved (w_H W) E _ ms regs gB_expect HS ltac:(vm_compute; reflexivity)).
  intros r Hr. cbv [CALLEE_SAVED In] in Hr. repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
  lazymatch goal with |- sv_denot _ (gB_expect ?q) = _ =>
    let e := eval vm_compute in (gB_expect q) in change (gB_expect q) with e end;
  first
  [ lazymatch goal with |- sv_denot _ (SOff 2 80) = _ =>
      apply bv_eq; rewrite denot_SOff, E2, Hsp0; unfold spZ; replace (bv_unsigned (getr regs 2) - 80 + 80) with (bv_unsigned (getr regs 2)) by lia;
      apply zcanon_id; unfold M64; apply u64_range end
  | lazymatch goal with |- sv_denot _ (SOff ?q 0) = _ =>
      let j := eval vm_compute in (q - 32)%nat in change q with (32 + j)%nat end;
    rewrite fsw_SOff0, EX; reflexivity
  | rewrite fsw_SOff0;
    lazymatch goal with |- ew _ ?q = _ regs ?r =>
      change q with (Z.to_nat (bv_unsigned r)); rewrite ER;
      rewrite Forall_forall in Hkeep; apply Hkeep; cbn [In]; repeat (first [left; reflexivity | right]) end ].
- exact FR.
- exact HG.
- replace (v + 32) with (v + 32 + 0) by lia.
  apply (fsw_field _ _ 9 _ _ _ _ _ _ 0 8%N (SOff 10 0) y' HRK ltac:(rewrite (ER 9%bv), H9; apply wz; lia)
    ltac:(cbn; tauto)); [rewrite fsw_SOff0, (ER 10%bv); exact H10 | cbn; lia | cbn; lia].
- replace (v + 48) with (v + 48 + 0) by lia.
  apply (fsw_field _ _ 8 _ _ _ _ _ _ 0 8%N (SOff 22 0) cap' HRC ltac:(rewrite (ER 8%bv), H8; apply wz; lia)
    ltac:(cbn; tauto)); [rewrite fsw_SOff0, (ER 22%bv); exact H22 | cbn; lia | cbn; lia].
- exact HJ.
- exact HARU.
Qed.
End WC.
