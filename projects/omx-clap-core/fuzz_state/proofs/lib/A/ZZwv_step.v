(* write_value's CONTAINER arms (fs.asan image A, write_value 0x83d84): one arm instance as a Section (the entry's
   fixed data F and memory, the entry facts as hypotheses), and the step every loop call ends with: from the facts at
   the call and the callee's post, the loop invariant ZZwv_inv.wvc_inv at the return point.
   Template (segmentation, not a copied proof): a working branch lib/A/Prog/write_value_cont.v
   (Section Body 146-207: the arm's fixed data and hypotheses; wvc_ind 657-693, wvc_ps 813-886, wvc_wv 889-993: a
   call and its next body invariant).
   Rule 24: no function proved here (write_value's lookup: lane record (internal path), CHECKER CONFIRM
   a Theorem Labs lane). *)
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
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat
FSH_Fn_writer FSH_Fn_alloc FSW_K FSW_K3 FSW_ret FSW_rres FSW_writer_tbl FSW_writer_model FSW_writer_kit
FSH_Fn_reader FSW_rd FSupoisonStack FSW_pj ZZwv_defs ZZwv_inv ZZwv_kit ZZwv_comp ZZwv_tree ZZwv_call ZZwv_call2
ZZwv_call3 ZZwv_res ZZwv_ret ZZwv_runs2.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterValue PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the pieces the arm writes *)
Definition wvc_WP (F : wvc_fix) : list (list Z) :=
  WriterValue.wvpieces (wf_t F) (negb (wf_p F =? 0)) (wf_d F).

(* ---- the loop state's register values, as the symbolic values wvc_ssL names ---- *)
Lemma wvc_den_val : forall E e z, U E e = z -> sv_denot E e = w64 z.
Proof. intros E e z H. rewrite denot_lit_U, H. reflexivity. Qed.

Lemma wvc_shv_U : forall E c v, ew E 9 = Z_to_bv 64 v -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  0 <= v + c -> v + c < 2 ^ 60 -> 0 <= v < 2 ^ 64 ->
  U E (wvc_shv 9 c) = (v + c) / 8 + SHADOW_OFF.
Proof.
intros E c v H9 H32 H0 H1 Hv. unfold wvc_shv.
rewrite U_SAlu, U_SAlu, U_SOff, U_SOff, U_SLit, H9, H32, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
cbn [zalu_raw]. unfold zcanon, M64.
rewrite (Z.mod_small (v + c)) by lia. rewrite (Z.mod_small 3) by lia.
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (Hd : 0 <= (v + c) / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (Z.mod_small ((v + c) / 8)) by lia. rewrite Z.add_0_r, (Z.mod_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
apply Z.mod_small. unfold SHADOW_OFF. lia.
Qed.

Lemma wvc_sub_U : forall E ke keys, ew E (xatom 18) = Z_to_bv 64 ke -> ew E (xatom 2) = Z_to_bv 64 keys ->
  0 <= keys <= ke -> ke < 2 ^ 64 ->
  U E (SAlu ALU_SUB (SOff (xatom 18) 0) (SOff (xatom 2) 0)) = ke - keys.
Proof.
intros E ke keys H18 H2 H0 H1.
rewrite U_SAlu, (U_atom E (xatom 18) ke H18 ltac:(lia)), (U_atom E (xatom 2) keys H2 ltac:(lia)).
cbn [zalu_raw]. unfold zcanon, M64. apply Z.mod_small. lia.
Qed.

Lemma wvc_d1_U : forall E d, ew E (xatom 4) = Z_to_bv 64 d -> 0 <= d -> d + 1 < 2 ^ 31 ->
  U E (SAlu ALU_ADD (SAluw ALU_ADD (SOff (xatom 4) 0) (SLit 1)) (SLit 0)) = d + 1.
Proof.
intros E d H Hd0 Hd1.
rewrite U_SAlu, (wvc_u_w1 E (xatom 4) d H Hd0 Hd1), U_SLit. cbn [zalu_raw]. unfold zcanon, M64.
rewrite (Z.mod_small 0) by lia. rewrite Z.add_0_r. apply Z.mod_small. lia.
Qed.

(* a callee-saved register, by its number (vm_compute mangles the range disjunct for lia) *)
Lemma wvc_cs_z : forall (q : bv 5) z, bv_unsigned q = z ->
  (z = 2 \/ z = 3 \/ z = 4 \/ z = 8 \/ z = 9 \/ 18 <= z <= 27) -> acallee_saved (bv_unsigned q).
Proof. intros q z E H. unfold acallee_saved. rewrite E. exact H. Qed.

Section A. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Hypothesis HSS : FsShadowSyms B.
(* the arm instance: its fixed data and the entry state *)
Variable F : wvc_fix.
Variables (ly0 : alayout) (S0 : astate) (U0 : list (Z * Z)) (W0 : world tfibsegs) (mem0 : word -> option byte)
  (md0 : Model) (regs0 : bvmap 5 word).
(* the entry facts the arms' callers discharge once *)
Hypothesis HE_sp16 : wf_sp F mod 16 = 0.
Hypothesis HE_ot16 : wf_ot F mod 16 = 0.
Hypothesis HE_oot : wf_o F + 32 <= wf_ot F.
Hypothesis HE_o8 : wf_o F mod 8 = 0.
Hypothesis HE_top : wf_ot F <= ly_top ly0.
Hypothesis HE_top47 : ly_top ly0 <= 2 ^ 47.
Hypothesis HE_lo : alloc_ceiling + STK_write_value (wf_m F) <= wf_sp F.
Hypothesis HE_gp : YK11.getr regs0 3%bv = w64 (as_gp B).
Hypothesis HE_tp : YK11.getr regs0 4%bv = w64 (as_tp B).
Hypothesis HE_cap0 : 0 <= wf_cap0 F.
Hypothesis HE_capl : wf_cap0 F <= wf_live F.
Hypothesis HE_cnt0 : 0 <= wf_cnt0 F.
Hypothesis HE_p : 0 <= wf_p F < alloc_ceiling.
Hypothesis HE_d : 0 <= wf_d F.
Hypothesis HE_dd : wf_d F + Z.of_nat (PjTree.depth (wf_t F)) <= 2 ^ 31 - 1.
Hypothesis HE_room : Z.of_nat (length (wf_text0 F)) + Z.of_nat (length (concat (wvc_WP F))) + 1 <= WMAX.
Hypothesis HE_bud : wbudget_pre S0 (wf_cap0 F) (wf_cnt0 F) (wf_live F) (WriterApp.putN (wvc_st0 F) (wvc_WP F)).
Hypothesis HE_frl : Z.of_nat (length (frames S0)) <= FRL_CRT_CALLEE.
Hypothesis HE_foot : forall x, wf_o F <= x < wf_ot F -> ~ PjStruct.pj_foot (wf_v F) (wf_D F) x.
Hypothesis HE_plain : jv_plain (wf_t F).
Hypothesis HE_ty :
  (wf_ty F = 5 /\ exists items, wf_t F = PjTree.JArr items /\ wf_n F = Z.of_nat (length items) /\ wf_keys F = 0) \/
  (wf_ty F = 6 /\ exists members, wf_t F = PjTree.JObj members /\ wf_n F = Z.of_nat (length members)).
Hypothesis HE_hdr : exists num capn,
  PjStruct.pj_hdr tfibsegs (rdW W0 mem0) (wf_v F) (wf_ty F) num (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) capn.
Hypothesis HE_n : 0 <= wf_n F < 2 ^ 54.
Hypothesis HE_kk : 0 <= wf_kids F /\ wf_kids F + 56 * wf_n F <= alloc_ceiling /\
                   0 <= wf_keys F /\ wf_keys F + 8 * wf_n F <= alloc_ceiling.

(* a container's depth is at least one, so the item depth d + 1 is an int32 *)
Lemma wvc_d1 : wf_d F + 1 < 2 ^ 31.
Proof.
destruct HE_ty as [(_ & items & Ht & _ & _) | (_ & members & Ht & _)];
  rewrite Ht in HE_dd; cbn [PjTree.depth] in HE_dd; lia.
Qed.

(* the node's header at any state of the arm: its bytes are the entry's *)
Lemma wvc_hdr_at : forall ly S U W m buf st,
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly S U W m buf st ->
  exists num capn,
    PjStruct.pj_hdr tfibsegs (rdW W m) (wf_v F) (wf_ty F) num (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) capn.
Proof.
intros ly S U W m buf st HSEM. destruct HE_hdr as (num & capn & H). exists num, capn.
apply (PjStruct.pj_hdr_eq tfibsegs (rdW W0 mem0)); [exact H|].
destruct HSEM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNB & _). exact HNB.
Qed.


(* the env at a loop resume point: the callee's registers and the arm's extras with the key slot ke and its key *)
Definition wvc_E (regs : bvmap 5 word) (ke key : Z) : env :=
  Ereg regs (fs_extraT ++ wvc_xs regs0 (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) (wf_d F) ke key).

Lemma wvc_E_x : forall regs ke key j, ew (wvc_E regs ke key) (xatom j) =
  nth j (wvc_xs regs0 (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) (wf_d F) ke key) (Z_to_bv 64 0).
Proof. intros regs ke key j. unfold wvc_E. apply fsw_ew_xatom. Qed.

Lemma wvc_E_r : forall regs ke key (r : bv 5) n, Z.of_nat n = bv_unsigned r -> ew (wvc_E regs ke key) n = getr regs r.
Proof. intros regs ke key r n H. unfold wvc_E. apply ew_Ereg_nat. exact H. Qed.

Lemma wvc_E_32 : forall regs ke key, ew (wvc_E regs ke key) 32 = Z_to_bv 64 SHADOW_OFF.
Proof. intros regs ke key. unfold wvc_E. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity. Qed.

(* the facts the arm's entry gives about the node's address *)
Lemma wvc_v_low : forall ly S U W mx md m buf st,
  AR tfibsegs B ly S W mx md ->
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly S U W m buf st -> 4096 <= wf_v F /\ wf_v F + 56 <= alloc_ceiling.
Proof.
intros ly S U W mx md m buf st HAR HSEM.
destruct HSEM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HPO & _).
exact (fsw_pobj_low B ly S W mx md m (wf_v F) HAR HPO).
Qed.

(* ================= the return of a loop call: the loop invariant at the return point ================= *)
Lemma wvc_ret_inv : forall r2 i' Pd Pc Rest ly S U (W : world tfibsegs) memC mdC buf regsC R0 ke key
    STKc peak ly' S' U' (W' : world tfibsegs) regs' mem' md' buf',
  wvc_WP F = Pd ++ Pc ++ Rest ->
  ajournal tfibsegs B (wvc_STK F) (wf_ot F) (wvc_FP F) ly0 S0 W0 (unpoison U0 mem0) md0 []
    ly S W (unpoison U memC) mdC (wevk (wf_cap0 F) (wvc_stP F Pd)) ->
  ARU tfibsegs B ly S U W memC mdC ->
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly S U W memC buf (wvc_stP F Pd) ->
  wf_peak0 F <= peak <= Z.max (wf_peak0 F) (wf_live F - wf_cap0 F + WriterApp.w_cap (wvc_stP F Pd)) ->
  Forall (YP09.chunk_ok tfibsegs (wvc_E R0 ke key) (rdW W memC) (wf_sp F - WVC_F)) (wvc_csL (wf_p F)) ->
  YK11.getr R0 9%bv = w64 (wf_v F) ->
  spZ regsC = wf_sp F - WVC_F ->
  YK11.getr regsC 8%bv = w64 (wf_o F) -> YK11.getr regsC 9%bv = w64 (wf_v F) ->
  YK11.getr regsC 19%bv = w64 (wf_p F) -> YK11.getr regsC 21%bv = w64 i' ->
  YK11.getr regsC 25%bv = w64 (56 * i') -> YK11.getr regsC 22%bv = w64 (8 * i') ->
  YK11.getr regsC 3%bv = YK11.getr regs0 3%bv -> YK11.getr regsC 4%bv = YK11.getr regs0 4%bv ->
  YK11.getr regsC 18%bv = w64 ((wf_v F + 40) / 8 + SHADOW_OFF) ->
  YK11.getr regsC 20%bv = w64 (wf_v F + 40) -> YK11.getr regsC 23%bv = w64 (wf_v F + 24) ->
  YK11.getr regsC 24%bv = w64 (wf_d F + 1) ->
  YK11.getr regsC 26%bv = w64 ((wf_v F + 24) / 8 + SHADOW_OFF) ->
  YK11.getr regsC 27%bv = w64 (wf_v F / 8 + SHADOW_OFF) ->
  0 <= i' < wf_n F ->
  ajournal tfibsegs B (STKc + (wf_ot F - spZ regsC)) (wf_ot F)
    (FS_PSTAT_FP ++ wbuf_fp buf (WriterApp.w_cap (wvc_stP F Pd))) ly S W (unpoison U memC) mdC []
    ly' S' W' (unpoison U' mem') md'
    (wevk (WriterApp.w_cap (wvc_stP F Pd)) (WriterApp.putN (wv_rst (wvc_stP F Pd)) Pc)) ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' -> aregs_preserved regsC regs' ->
  0 <= STKc -> STKc + WVC_F <= STK_write_value (wf_m F) ->
  uswap U U' buf buf' (WriterApp.w_cap (wvc_stP F Pd)) ->
  wout_ok B tfibsegs ly' S' W' mem' (wf_o F) buf' (WriterApp.w_cap (WriterApp.putN (wv_rst (wvc_stP F Pd)) Pc))
    (WriterApp.w_failed (WriterApp.putN (wv_rst (wvc_stP F Pd)) Pc))
    (WriterApp.w_text (WriterApp.putN (wv_rst (wvc_stP F Pd)) Pc)) ->
  wbudget_kept S S' (WriterApp.w_failed (wvc_stP F Pd)) (WriterApp.w_cap (wvc_stP F Pd))
    (WriterApp.w_cnt (wvc_stP F Pd))
    (WriterApp.w_failed (WriterApp.putN (wv_rst (wvc_stP F Pd)) Pc))
    (WriterApp.w_cap (WriterApp.putN (wv_rst (wvc_stP F Pd)) Pc))
    (WriterApp.w_cnt (WriterApp.putN (wv_rst (wvc_stP F Pd)) Pc)) ->
  bswap (ablocks B ly S) (ablocks B ly' S') buf buf' (WriterApp.w_cap (wvc_stP F Pd))
    (WriterApp.w_cap (WriterApp.putN (wv_rst (wvc_stP F Pd)) Pc)) ->
  wkeep tfibsegs W W' memC mem' (spZ regsC) (wf_ot F) (wf_o F) 32 ->
  (exists peak', peak <= peak' <= Z.max peak ((wf_live F + WriterApp.w_cap (wvc_stP F Pd) - wf_cap0 F) -
                    WriterApp.w_cap (wvc_stP F Pd) + WriterApp.w_cap (WriterApp.putN (wv_rst (wvc_stP F Pd)) Pc)) /\
     fs_glob tfibsegs W' mem' ((wf_live F + WriterApp.w_cap (wvc_stP F Pd) - wf_cap0 F) +
       WriterApp.w_cap (WriterApp.putN (wv_rst (wvc_stP F Pd)) Pc) - WriterApp.w_cap (wvc_stP F Pd)) peak'
       (WriterApp.w_cnt (WriterApp.putN (wv_rst (wvc_stP F Pd)) Pc))
       (WriterApp.w_fail (WriterApp.putN (wv_rst (wvc_stP F Pd)) Pc))) ->
  exists key', wvc_inv B F r2 i' (wf_keys F + 8 * i') key' (Pd ++ Pc) ly0 S0 U0 W0 mem0 md0 regs0
    W' (mkst regs' (Z_to_bv 64 r2) mem' (seg_rom tfibsegs)) md' ly' S' U' buf'.
Proof.
intros r2 i' Pd Pc Rest ly S U W memC mdC buf regsC R0 ke key STKc peak ly' S' U' W' regs' mem' md' buf'
  HWP HJ HARU HSEM Hpk HCH HR09 Hsp R8 R9 R19 R21 R25 R22 R3 R4 R18 R20 R23 R24 R26 R27 Hi
  HJc OK' PO' HP HSTK0 HSTKc HUS' HOUT' HBK' HBS' HWK' HGL'.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HWF : WVC_F = 176) by reflexivity.
pose proof (wvc_stk (wf_m F)) as (HSTKF & _).
pose proof (wvc_sem_o_sp B F ly0 S0 U0 W0 mem0 regs0 ly S U W memC buf _ HSEM) as Hosp.
pose proof (proj1 HARU) as HAR.
pose proof (wvc_v_low ly S U W (unpoison U memC) mdC memC buf _ HAR HSEM) as (Hv1 & Hv2).
assert (Hlo' : alloc_ceiling <= wf_sp F - WVC_F) by lia.
set (st := wvc_stP F Pd) in *.
(* the count stays below 2^64, the cap only grows from the entry's *)
assert (Hcnt : wf_cnt0 F + wcalls (WriterApp.putN st Pc) < 2 ^ 64).
{ pose proof HE_bud as (_ & _ & _ & HB4). rewrite HWP, app_assoc, WriterApp.putN_app, WriterApp.putN_app in HB4.
  pose proof (zzwv_calls_mono Rest (WriterApp.putN (WriterApp.putN (wvc_st0 F) Pd) Pc)) as M.
  unfold st, wvc_stP in *. lia. }
assert (Hcap0i : wf_cap0 F <= WriterApp.w_cap st) by exact (wv_cap_mono (wvc_st0 F) Pd HE_cap0).
(* the writer facts at the return *)
destruct (wvc_sem_call B F ly0 S0 U0 W0 mem0 regs0 ly S U W memC mdC buf st Pc ly' S' U' W' mem' md' buf'
  (STKc + (wf_ot F - spZ regsC)) _ (spZ regsC) peak HSEM HARU HE_cap0 Hcap0i HE_cnt0 Hcnt Hlo' HE_oot Hpk HJc OK' PO'
  HUS' HOUT' HBK' HBS' HWK' ltac:(lia) HGL') as (HARU' & HSEM').
pose proof HSEM as (HOUT & _ & _ & _ & HBS & _ & _ & _ & _ & _ & _ & _ & _ & _ & HBIN & _).
pose proof HOUT as (_ & _ & _ & _ & _ & Hcap64 & _).
pose proof HSEM' as (_ & _ & HHD' & _ & _ & _ & _ & _ & HN' & HPO' & HNB' & HUL' & HDb' & _).
destruct (wvc_hdr_at ly' S' U' W' mem' buf' _ HSEM') as (num & capn & HHDR').
(* the journal's footprint at the call *)
pose proof (wv_fp_sub_swap B ly0 S0 ly S W (unpoison U memC) mdC (wf_buf0 F) (wf_cap0 F) buf (WriterApp.w_cap st)
  HAR HBS HBIN ltac:(lia) wvc_pstat_img) as HFPSUB.
(* the key slot of an object, at the return memory *)
assert (Hrs : forall q : bv 5, acallee_saved (bv_unsigned q) -> getr regs' q = getr regsC q)
  by (intros q Hq; exact (fsw_pres regsC regs' q HP Hq)).
assert (HK : exists key', wf_ty F = 6 ->
  PjStruct.pj_u64 tfibsegs (rdW W' mem') (wf_keys F + 8 * i') key' /\
  (exists P q, In (P, q) (ablocks B ly' S') /\ P + 16 <= wf_keys F + 8 * i' /\
     wf_keys F + 8 * i' + 8 <= P + req_size q) /\
  (wf_keys F + 8 * i') mod 8 = 0 /\
  (forall x, wf_keys F + 8 * i' <= x < wf_keys F + 8 * i' + 8 -> ~ (wf_v F <= x < wf_v F + 56))).
{ destruct HE_ty as [(Hty & _) | (Hty & members & Ht & Hn)]; [exists 0; intros E; rewrite Hty in E; discriminate|].
  rewrite Ht in HN'.
  destruct (nth_error members (Z.to_nat i')) as [[nm u]|] eqn:Enth.
  2: { exfalso. apply nth_error_None in Enth. lia. }
  destruct (wv_obj_mem _ _ _ _ _ _ _ _ HN' Enth) as (num2 & kids2 & keys2 & n2 & cap2 & Di & Dpre & x & kk & Du &
    Dpost & HH2 & En2 & Hnc & Hc2 & _ & _ & ED & _ & Hx & _ & _ & _ & _ & _).
  assert (Ekeys : keys2 = wf_keys F).
  { destruct HH2 as (_ & _ & _ & _ & _ & Hk2 & _). destruct HHDR' as (_ & _ & _ & _ & _ & Hk1 & _).
    exact (PjStruct.pj_u64_uniq _ _ _ _ _ Hk2 Hk1). }
  subst keys2. rewrite Z2Nat.id in Hx by lia.
  exists x. intros _. split; [exact Hx|].
  assert (Hin : In (wf_keys F, 8 * cap2) (wf_D F)) by (rewrite ED; right; left; reflexivity).
  destruct (HUL' _ _ Hin) as (Hblk & H16 & Hk & _).
  split.
  { exists (wf_keys F - HEAD), (8 * cap2 + HEAD). split; [exact Hblk|].
    pose proof (req_size_pos (8 * cap2 + HEAD) ltac:(unfold HEAD; lia)) as (_ & RQ). unfold HEAD in *. lia. }
  split.
  { apply Z.mod_divide in H16 as [q Hq]; [|lia]. rewrite Hq.
    replace (q * 16 + 8 * i') with ((2 * q + i') * 8) by lia. apply Z_mod_mult. }
  destruct HN' as (_ & Hap & _). intros y Hy. apply (Hap (wf_keys F, 8 * cap2) y Hin).
  unfold PjStruct.pj_holds. cbn [fst snd]. lia. }
destruct HK as (key' & HK).
exists key'.
set (E' := wvc_E regs' (wf_keys F + 8 * i') key').
assert (E2' : bv_unsigned (ew E' 2) = wf_sp F - WVC_F).
{ unfold E'. rewrite (wvc_E_r regs' _ _ 2%bv 2 eq_refl), (Hrs 2%bv ltac:(apply (wvc_cs_z _ 2); [reflexivity | lia])).
  exact Hsp. }
assert (E9' : ew E' 9 = Z_to_bv 64 (wf_v F)).
{ unfold E'. rewrite (wvc_E_r regs' _ _ 9%bv 9 eq_refl), (Hrs 9%bv ltac:(apply (wvc_cs_z _ 9); [reflexivity | lia])).
  exact R9. }
assert (E19' : ew E' 19 = Z_to_bv 64 (wf_p F)).
{ unfold E'. rewrite (wvc_E_r regs' _ _ 19%bv 19 eq_refl), (Hrs 19%bv ltac:(apply (wvc_cs_z _ 19); [reflexivity | lia])).
  exact R19. }
assert (E32' : ew E' 32 = Z_to_bv 64 SHADOW_OFF) by (unfold E'; apply wvc_E_32).
assert (EX : forall j, ew E' (xatom j) =
  nth j (wvc_xs regs0 (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) (wf_d F) (wf_keys F + 8 * i') key')
    (Z_to_bv 64 0)) by (intros j; unfold E'; apply wvc_E_x).
(* the frame chunks at the return, in the return env *)
assert (HCH' : Forall (YP09.chunk_ok tfibsegs E' (rdW W' mem') (wf_sp F - WVC_F)) (wvc_csL (wf_p F))).
{ apply (wvc_csL_after (wvc_E R0 ke key) E' W W' memC mem' (wf_sp F) (spZ regsC) (wf_ot F) (wf_o F) (wf_p F)
    HCH HWK'); [lia | lia | lia | | |].
  - rewrite E9', (wvc_E_r R0 ke key 9%bv 9 eq_refl). symmetry. exact HR09.
  - rewrite E32'. unfold wvc_E. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity.
  - intros j Hj. rewrite EX, wvc_E_x.
    do 18 (destruct j as [|j]; [cbn [nth wvc_xs app map]; reflexivity|]). exfalso. lia. }
(* the regions of the loop state at the return *)
destruct (wvc_resume_rs B ly' S' U' W' mem' md' E' (wf_ty F) (wf_p F) (wf_v F) num (wf_str F) (wf_kids F)
  (wf_keys F) (wf_n F) capn (wf_sp F) (wf_keys F + 8 * i') key'
  ltac:(destruct HE_ty as [(Hty & _) | (Hty & _)]; [left | right]; exact Hty)
  HARU' HHD' HPO' HHDR' E2' Hlo' ltac:(lia) E9' E32'
  ltac:(rewrite EX; reflexivity) ltac:(rewrite EX; reflexivity)
  ltac:(rewrite EX; reflexivity) ltac:(rewrite EX; reflexivity)
  ltac:(intros Hty; destruct (HK Hty) as (Hu & Hb & Hm & Ha);
        split; [rewrite EX; reflexivity|];
        split; [rewrite EX; reflexivity|];
        split; [exact Hu|]; split; [exact Hb|]; split; [exact Hm | exact Ha]))
  as (HRS & HPD & HGF & HSH).
(* the after-call step *)
destruct (wvc_after_call2 B (wvc_STK F) (wf_ot F) (wvc_FP F) [] ly0 S0 U0 W0 W mem0 md0 ly S U memC mdC
  (wevk (wf_cap0 F) st) STKc (FS_PSTAT_FP ++ wbuf_fp buf (WriterApp.w_cap st)) (wf_ot F) WVC_F regsC ly' S' U' W'
  regs' mem' md' (wevk (WriterApp.w_cap st) (WriterApp.putN (wv_rst st) Pc))
  (wvc_xs regs0 (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) (wf_d F) (wf_keys F + 8 * i') key')
  (wvc_csL (wf_p F)) (wvc_rsL (wf_ty F)) (wvc_gfL (wf_ty F)) r2 (wf_sp F) HSS HJ HARU HJc HFPSUB OK' PO' HP Hsp
  ltac:(unfold WVC_F; lia) HSTK0 ltac:(unfold wvc_STK; lia) ltac:(reflexivity) HE_sp16
  ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(apply wvc_rsL_wf; destruct HE_ty as [(Hty & _) | (Hty & _)]; [left | right]; exact Hty)
  HCH' HRS HPD HGF) as (HJ' & HARU'' & HST).
(* the loop state *)
assert (Hval : forall (q : bv 5) z, acallee_saved (bv_unsigned q) -> getr regsC q = w64 z ->
  YK11.getr (ms_regs (mkst regs' (Z_to_bv 64 r2) mem' (seg_rom tfibsegs))) q = w64 z).
{ intros q z Hq E. cbn [ms_regs mkst]. rewrite (Hrs q Hq). exact E. }
assert (HSL : st_ok tfibsegs E' (wvc_ssL (wf_ty F) (wf_p F) r2)
  (restrict (w_H W') (mkst regs' (Z_to_bv 64 r2) mem' (seg_rom tfibsegs)))).
{ apply (wvc_ssL_ret E' (wf_ty F) (wf_p F) r2 _ (wf_n F) HST).
  - cbn [ms_regs restrict mkst]; rewrite (Hrs 18%bv ltac:(apply (wvc_cs_z _ 18); [reflexivity | lia])), R18,
      (wvc_den_val E' (wvc_shv 9 40) _ (wvc_shv_U E' 40 (wf_v F) E9' E32' ltac:(lia) ltac:(lia) ltac:(lia))).
    reflexivity.
  - cbn [ms_regs restrict mkst]; rewrite (Hrs 20%bv ltac:(apply (wvc_cs_z _ 20); [reflexivity | lia])), R20,
      (wvc_den_val E' (SOff 9 40) _ (wvc_u_off E' 9 (wf_v F) 40 E9' ltac:(lia) ltac:(lia))).
    reflexivity.
  - cbn [ms_regs restrict mkst]; rewrite (Hrs 22%bv ltac:(apply (wvc_cs_z _ 22); [reflexivity | lia])), R22,
      (wvc_den_val E' _ _ (wvc_sub_U E' (wf_keys F + 8 * i') (wf_keys F) ltac:(rewrite EX; reflexivity)
         ltac:(rewrite EX; reflexivity) ltac:(lia) ltac:(lia))).
    unfold w64. f_equal. lia.
  - cbn [ms_regs restrict mkst]; rewrite (Hrs 23%bv ltac:(apply (wvc_cs_z _ 23); [reflexivity | lia])), R23,
      (wvc_den_val E' (SOff 9 24) _ (wvc_u_off E' 9 (wf_v F) 24 E9' ltac:(lia) ltac:(lia))).
    reflexivity.
  - cbn [ms_regs restrict mkst]; rewrite (Hrs 24%bv ltac:(apply (wvc_cs_z _ 24); [reflexivity | lia])), R24,
      (wvc_den_val E' _ _ (wvc_d1_U E' (wf_d F) ltac:(rewrite EX; reflexivity) HE_d
         wvc_d1)).
    reflexivity.
  - cbn [ms_regs restrict mkst]; rewrite (Hrs 26%bv ltac:(apply (wvc_cs_z _ 26); [reflexivity | lia])), R26,
      (wvc_den_val E' (wvc_shv 9 24) _ (wvc_shv_U E' 24 (wf_v F) E9' E32' ltac:(lia) ltac:(lia) ltac:(lia))).
    reflexivity.
  - cbn [ms_regs restrict mkst]; rewrite (Hrs 27%bv ltac:(apply (wvc_cs_z _ 27); [reflexivity | lia])), R27,
      (wvc_den_val E' (wvc_shv 9 0) _ (wvc_shv_U E' 0 (wf_v F) E9' E32' ltac:(lia) ltac:(lia) ltac:(lia))).
    rewrite Z.add_0_r. reflexivity.
  - exact E19'.
  - lia.
  - rewrite EX. reflexivity.
  - lia. }
unfold wvc_inv. cbv zeta. fold E'.
split.
{ split; [exact HSL|]. split; [exact HSH|].
  split.
  - assert (ESP : wevk (wf_cap0 F) (WriterApp.putN (wvc_st0 F) (Pd ++ Pc))
       = wevk (wf_cap0 F) st
         + wevk (WriterApp.w_cap st) (WriterApp.putN (wv_rst st) Pc))
      by exact (wv_wevk_split (wvc_st0 F) Pd Pc eq_refl HE_cap0).
    unfold wvc_stP. rewrite ESP. exact HJ'.
  - exact HARU''. }
split.
{ unfold wvc_stP. rewrite WriterApp.putN_app. cbn [ms_mem mkst]. exact HSEM'. }
split; [exact (Hval 8%bv _ ltac:(apply (wvc_cs_z _ 8); [reflexivity | lia]) R8)|].
split; [exact (Hval 9%bv _ ltac:(apply (wvc_cs_z _ 9); [reflexivity | lia]) R9)|].
split; [exact (Hval 19%bv _ ltac:(apply (wvc_cs_z _ 19); [reflexivity | lia]) R19)|].
split; [exact (Hval 21%bv _ ltac:(apply (wvc_cs_z _ 21); [reflexivity | lia]) R21)|].
split; [exact (Hval 25%bv _ ltac:(apply (wvc_cs_z _ 25); [reflexivity | lia]) R25)|].
split; [cbn [ms_regs mkst]; rewrite (Hrs 3%bv ltac:(apply (wvc_cs_z _ 3); [reflexivity | lia])); exact R3|].
split; [cbn [ms_regs mkst]; rewrite (Hrs 4%bv ltac:(apply (wvc_cs_z _ 4); [reflexivity | lia])); exact R4|].
split; [exact (Hval 18%bv _ ltac:(apply (wvc_cs_z _ 18); [reflexivity | lia]) R18)|].
split; [exact (Hval 20%bv _ ltac:(apply (wvc_cs_z _ 20); [reflexivity | lia]) R20)|].
split; [exact (Hval 22%bv _ ltac:(apply (wvc_cs_z _ 22); [reflexivity | lia]) R22)|].
split; [exact (Hval 23%bv _ ltac:(apply (wvc_cs_z _ 23); [reflexivity | lia]) R23)|].
split; [exact (Hval 24%bv _ ltac:(apply (wvc_cs_z _ 24); [reflexivity | lia]) R24)|].
split; [exact (Hval 26%bv _ ltac:(apply (wvc_cs_z _ 26); [reflexivity | lia]) R26)|].
split; [exact (Hval 27%bv _ ltac:(apply (wvc_cs_z _ 27); [reflexivity | lia]) R27)|].
split.
{ cbn [ms_regs mkst]. unfold spZ. rewrite (Hrs 2%bv ltac:(apply (wvc_cs_z _ 2); [reflexivity | lia])). exact Hsp. }
split; [exact Hi | reflexivity].
Qed.

End A.
