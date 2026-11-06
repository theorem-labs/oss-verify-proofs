(* fs ASan, group ALLOC: the walk of fuzz_malloc (A 0x828ac, alloc.c:61-66 with own() :41-49 inlined), proving
   fuzz_malloc_spec of lib/A/FSH_Fn_alloc.v over fs.asan (image tfibsegs).

   Measured control flow (capstone on the unstripped twin of the pinned fuzz_state.asan, sha256 64b53ff8...):
   0x828ac..0x828bc frame + save ra / s0 / s1 / s2; s0 = n; s2 = the shadow base (GOT word 0x9f6f0 -> cell 0xa7f38);
   a3 = g_count, a4 = g_fail_at; g_count := a3 + 1 (0x828e4); `bne a3, a4` 0x828e8.
   - NULL arm (failing(): cnt = fail): g_fail_at := -1 (0x828f4), a0 = 0, epilogue, ret 0x829c0.
   - malloc arm: `bltu -17, s0` (never taken, n < MALLOC_MAX); `jal __wrap_malloc` 0x82908 (ra 0x8290c) with
     a0 = n + 16; `beqz a0` (never taken: the call is non-NULL); s1 = b; own(): the two inline shadow checks of the head
     (0x82914..0x82934), the 8 `sb` of n into the head (0x82950..0x82970), `jal __asan_poison_memory_region` 0x8297c
     (ra 0x82980) with (b, 16); g_live += n (0x82994), g_peak := max (0x8299c); a0 = b + 16; epilogue; ret 0x829c0.

   Shape (a Theorem Labs lane's FSW_strdup.v; another Theorem Labs lane's FSW_realloc.v fsr_p0): entry FSW_statics.fsw_entryTS, runs by
   FSW_K.fsw_aj_runU whose awr_ok is FSW_statics_awr.fsw_awr_TS (kit rule R2), branches by SRr_sym_branch, the return by
   FSW_ret.fsw_retU, fs_glob read back by FSW_statics.fs_glob_of_TS. The control-flow template is the released plain
   proof lib/Prog/fuzz_malloc_c.v (NULL / own arms; no lemma imported, no lib/Prog import). Kit rules R1 (per-goal
   `first [solve ..]`, computing alternatives guarded by goal shape) and R2 are followed. Relocated files: none. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG08 YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q YG05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w AF0l AF0m FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSH_Fn_alloc
FSW_K FSW_K3 FSW_ret FSW_rres FSW_rd FSW_statics FSW_statics_awr FSW_head FSW_malloc_free
FSpoisonS FSpoisonR FSpoisonW FSW_poison_conv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Lemma fm_tbl_ret : clookup tbl_fm 0x829c0 = Some RET_WORD_r.
Proof. vm_compute. reflexivity. Qed.

(* awr_ok sees a region list only through its skeleton (base and write window), so a run from a later state of the
   same walk (its chunks changed, not its regions) inherits the entry's awr_ok *)
Lemma fm_awr_skel : forall segs B E rs rs' STK sp0 FP bl0 blc ly own fr0,
  skeleton rs' = skeleton rs ->
  awr_ok segs B E rs STK sp0 FP bl0 blc ly own fr0 -> awr_ok segs B E rs' STK sp0 FP bl0 blc ly own fr0.
Proof. intros segs B E rs rs' STK sp0 FP bl0 blc ly own fr0 Hsk H a Ha. apply H. exact (in_wrange_skeleton E rs' rs a Hsk Ha). Qed.

(* the GOT word 0x9f6f0 and the shadow cell 0xa7f38 of fs.asan are image bytes (FSW_statics.fs_pstat_img's method) *)
Definition FM_CELLS : list (Z * Z) := [(0x9f6f0, 0x9f6f8); (0xa7f38, 0xa7f40)].
Lemma fm_cells_img : forall a, inFP FM_CELLS a -> in_img tfibsegs a.
Proof.
intros a (r & Hr & Ha).
assert (Hb : forallb (fun r : Z * Z => existsb (fun s => (Z.of_N (seg_base s) <=? fst r) &&
    (snd r <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs) FM_CELLS = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) Hb r Hr) as H. cbv beta in H.
apply existsb_exists in H as (s & Hs & Hss). apply andb_prop in Hss as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists s. split; [exact Hs | lia].
Qed.

(* an 8-byte (any width) value chunk read under one env and base is the same chunk under another env and base when the
   absolute address and the value agree (CVal's bytes do not depend on the address) *)
Lemma fm_chunk_move : forall E E' m base base' off off' sz e e',
  base + off = base' + off' -> sv_denot E e = sv_denot E' e' ->
  YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal sz e)) ->
  YP09.chunk_ok tfibsegs E' m base' (YP09.mkChunk off' (CVal sz e')).
Proof.
intros E E' m base base' off off' sz e e' Hb He H i Hi. destruct (H i Hi) as (b & H1 & H2). exists b.
cbn [cbyte YP09.c_off YP09.c_val] in *. rewrite <- He, <- Hb. split; [exact H1 | exact H2].
Qed.

(* FSW_statics.fs_pstat_regions_ok under an env with further atoms after the statics' (a resumed state's extra atoms
   for the saved frame values); same proof *)
Lemma fm_pstat_ok : forall (W : world tfibsegs) regs mem live peak cnt fail ys,
  fs_glob tfibsegs W mem live peak cnt fail ->
  Forall (region_ok tfibsegs (Ereg regs (fs_extraTS cnt fail live peak ++ ys)) (mrestrict (w_H W) mem)) fs_pstat_regions.
Proof.
intros W regs mem live peak cnt fail ys GL.
pose proof GL as (G1 & G2 & G3 & G4 & GR).
set (E := Ereg regs (fs_extraTS cnt fail live peak ++ ys)).
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (fs_extraTS cnt fail live peak) (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite ew_Ereg_extra; apply app_nth1; cbn; lia).
assert (RS : forall g (j : nat) v, (1 <= j < 5)%nat -> nth j (fs_extraTS cnt fail live peak) (Z_to_bv 64 0) = Z_to_bv 64 v ->
  0 <= v < 2 ^ 64 -> 0x9f000 <= g -> g + 8 <= 0x5fd000 -> val_mem tfibsegs (mrestrict (w_H W) mem) g 8 v ->
  region_ok tfibsegs E (mrestrict (w_H W) mem) (fs_pstat_region g (32 + j))).
{ intros g j v Hj Hv Hr Hg1 Hg2 Hm.
  unfold region_ok, fs_pstat_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  split; [lia|]. split; [lia|]. split.
  - intros o Ho. unfold writable_at. apply AB13.tfib_rw_window. rewrite unsigned_lit_small by lia. lia.
  - constructor; [|constructor].
    exact (chunk_ok_val tfibsegs _ _ 0 g 8 (SOff (32 + j) 0) v
      ltac:(rewrite fsw_SOff0; etransitivity; [exact (EX j ltac:(lia)) | exact Hv]) ltac:(cbn [Z.of_N]; lia)
      ltac:(cbn [Z.of_N]; lia) ltac:(cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Hm)). }
unfold fs_pstat_regions, xatom.
constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- apply (RS G_COUNT 1%nat cnt); first [solve [lia] | solve [reflexivity] | solve [unfold G_COUNT; lia] | solve [exact G3]].
- apply (RS G_FAIL 2%nat fail); first [solve [lia] | solve [reflexivity] | solve [unfold G_FAIL; lia] | solve [exact G4]].
- apply (RS G_LIVE 3%nat live); first [solve [lia] | solve [reflexivity] | solve [unfold G_LIVE; lia] | solve [exact G1]].
- apply (RS G_PEAK 4%nat peak); first [solve [lia] | solve [reflexivity] | solve [unfold G_PEAK; lia] | solve [exact G2]].
Qed.

Section n. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* fs's image facts (FSH_Rt.fs_img_facts); owner RELOC, proved once for fs's TfibB; used for awr_byte's static arm *)
Hypothesis IMG : fs_img_facts tfibsegs B.
(* the two shadow-base cells of fs.asan (GOT word 0x9f6f0 holds the cell 0xa7f38 = __asan_shadow_memory_dynamic_address),
   FSW_K.fsw_entryT's premises: FSH_Base.FsShadowSyms, the one named shadow-cell hypothesis of fs's walks, discharged by
   lib/A/ACeg.v's TfibLib (owner RELOC / S0 start-up layer) *)
Hypothesis SHS : FsShadowSyms B.
Let FS_GOT_SHADOW : as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address := proj1 SHS.
Let FS_SHADOW_CELL : as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address := proj2 SHS.

(* the NULL arm of fuzz_malloc_spec (failing(): cnt = fail): g_count := cnt + 1, g_fail_at := SIZE_MAX, a0 = 0 *)
Lemma fm_null_arm : forall ly S U (W : world tfibsegs) regs mem md ch live peak cnt fail,
  fpreU tfibsegs B STK_fuzz_malloc ly S U W regs mem md ch -> fs_heads B ly S U ->
  fs_glob tfibsegs W mem live peak cnt fail -> cnt + 1 < 2 ^ 64 -> cnt = fail ->
  SRr tfibsegs W (cfg_at tfibsegs A_fuzz_malloc regs mem md)
    (apost_baseU tfibsegs B STK_fuzz_malloc FS_PSTAT_FP regs ly S W mem md 0 U U
       (fun ly' S' W' regs' mem' md' =>
          getr regs' 10 = w64 0 /\ ablocks B ly' S' = ablocks B ly S /\
          fs_heads B ly' S' U /\
          fs_glob tfibsegs W' mem' live peak (cnt + 1) SIZE_MAXZ)).
Proof.
intros ly S U W regs mem md ch live peak cnt fail HPRE FH HGL Hcn Hcf.
pose proof HPRE as (HAP & HRO).
pose proof (fsw_ARU B STK_fuzz_malloc ly S U W regs mem md ch HAP) as HARU.
pose proof HAP as (HAN & _ & _).
pose proof HAN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof HGL as (_ & _ & _ & _ & Hlp & Hp64 & Hc64 & Hf64).
assert (FM : STK_fuzz_malloc = 16416) by reflexivity.
pose proof (fsw_entryTS B STK_fuzz_malloc 32 ly S U W regs mem md ch A_fuzz_malloc live peak cnt fail
  FS_GOT_SHADOW FS_SHADOW_CELL HAP ltac:(rewrite FM; lia) ltac:(vm_compute; reflexivity) HGL) as HS.
pose proof (ajournal_init tfibsegs B STK_fuzz_malloc FS_PSTAT_FP ly S W regs (unpoison U mem) md ch HAN) as HJ.
set (E := Ereg regs (fs_extraTS cnt fail live peak)) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (EX : forall j v, (j < 5)%nat -> nth j (fs_extraTS cnt fail live peak) (Z_to_bv 64 0) = Z_to_bv 64 v ->
  ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj Hv; subst E; rewrite ew_Ereg_extra; exact Hv).
assert (A0 : forall pc f FPx bl0 blc lyx own fr0, (forall a, inFP FS_PSTAT_FP a -> inFP FPx a) -> 0 <= f <= STK_fuzz_malloc ->
  awr_ok tfibsegs B E (ss_mem (fss0TS pc f)) STK_fuzz_malloc (spZ regs) FPx bl0 blc lyx own fr0)
  by (intros pc f FPx bl0 blc lyx own fr0 HFP Hf; exact (fsw_awr_TS B IMG E pc f STK_fuzz_malloc (spZ regs) FPx bl0 blc lyx own fr0 Usp ltac:(lia) HFP)).
unfold cfg_at. change (w64 A_fuzz_malloc) with (Z_to_bv 64 A_fuzz_malloc).
(* 0x828ac..0x828e4: frame, saves, s0 = n, s2 = shadow base, g_count := cnt + 1; stops at `bne a3, a4` *)
fsw_aj_runU tbl_fm_ok HS HJ HARU.
{ exact (A0 A_fuzz_malloc 32 FS_PSTAT_FP _ _ _ _ _ (fun a H => H) ltac:(lia)). }
clear HF HFr HG.
eapply SRr_sym_branch with (c := BC_NE) (a := SOff 33 0) (b := SOff 34 0) (1 := HS).
- (* taken: cnt <> fail, refuted *)
  intros Hb _. exfalso.
  rewrite branch_ne_U, (U_atom E 33 cnt (EX 1%nat cnt ltac:(lia) eq_refl) Hc64),
    (U_atom E 34 fail (EX 2%nat fail ltac:(lia) eq_refl) Hf64), Hcf, Z.eqb_refl in Hb.
  discriminate Hb.
- (* not taken: cnt = fail; 0x828ec..0x829bc: a0 = 0, g_fail_at := -1, epilogue; stops at ret 0x829c0 *)
  intros _ HS2. clear HS.
  fsw_aj_runU tbl_fm_ok HS2 HJ HARU.
  { eapply fm_awr_skel; [| exact (A0 A_fuzz_malloc 32 FS_PSTAT_FP _ _ _ _ _ (fun a H => H) ltac:(lia))].
    lazymatch goal with |- skeleton _ = skeleton _ => vm_compute; reflexivity end. }
  pose proof HS2 as HS2c.
  destruct HS2c as (_ & _ & _ & _ & _ & _ & _ & HMEM & _).
  rreg HS2 (1%bv : bv 5) R1.
  rreg HS2 (10%bv : bv 5) R10.
  rewrite ?wvb_collapse in HJ, HARU.
  unfold apost_baseU.
  eapply (fsw_retU B tbl_fm tbl_fm_ok).
  all: first
    [ solve [exact HS2] | solve [exact HJ] | solve [exact HARU]
    | solve [lazymatch goal with |- ss_resv _ = None => reflexivity end]
    | solve [lazymatch goal with |- clookup _ _ = Some _ => vm_compute; reflexivity end]
    | solve [rewrite R1, ?fsw_SOff0, E1; exact Hra]
    | solve [eapply (aregs_preserved_of_st_ok tfibsegs _ E _ _ regs (fs_extraTS cnt fail live peak) HS2);
             first [ solve [apply env_agree_refl]
                   | solve [lazymatch goal with |- forallb _ _ = true => vm_compute; reflexivity end] ]]
    | idtac ].
  intros mat1. cbv beta.
  split; [rewrite R10; reflexivity|]. split; [reflexivity|]. split; [exact FH|].
  assert (E33 : ew E 33 = Z_to_bv 64 cnt) by exact (EX 1%nat cnt ltac:(lia) eq_refl).
  apply (fs_glob_of_TS E W _ _ live peak (cnt + 1) SIZE_MAXZ (SOff 35 0) (SOff 36 0) (SOff 33 1) (SLit SIZE_MAXZ) HMEM).
  all: first
    [ solve [lazymatch goal with |- fs_pstat_find _ _ = Some _ => vm_compute; reflexivity end]
    | solve [rewrite fsw_SOff0; exact (EX 3%nat live ltac:(lia) eq_refl)]
    | solve [rewrite fsw_SOff0; exact (EX 4%nat peak ltac:(lia) eq_refl)]
    | solve [lazymatch goal with |- sv_denot _ (SOff 33 1) = _ =>
               apply bv_eq; rewrite denot_SOff, E33; rewrite !unsigned_lit_small by lia;
               apply zcanon_id; unfold M64; lia end]
    | solve [lazymatch goal with |- sv_denot _ (SLit _) = _ => reflexivity end]
    | solve [unfold SIZE_MAXZ; lia]
    | solve [lia] ].
Qed.

End n.

(* the return address of fuzz_malloc's `jal __wrap_malloc` (A 0x82908; MEASURED) and of its poison call (0x8297c) *)
Definition A_fuzz_malloc_ra : Z := 0x8290c.
Definition A_fuzz_malloc_ra_po : Z := 0x82980.

(* own()'s 8 `sb` of n into the head, as the token run leaves them (MEASURED, the state at 0x8297c): byte k of the head
   is the low byte of n >> 8k, n being atom 8 (s0) *)
Definition fm_head_cs : list YP09.chunk :=
  [YP09.mkChunk 3 (CVal 1 (SAlu ALU_SRL (SOff 8 0) (SLit 24)));
   YP09.mkChunk 2 (CVal 1 (SAlu ALU_SRL (SOff 8 0) (SLit 16)));
   YP09.mkChunk 1 (CVal 1 (SAlu ALU_SRL (SOff 8 0) (SLit 8)));
   YP09.mkChunk 0 (CVal 1 (SOff 8 0));
   YP09.mkChunk 7 (CVal 1 (SAlu ALU_SRL (SOff 8 0) (SLit 56)));
   YP09.mkChunk 6 (CVal 1 (SAlu ALU_SRL (SOff 8 0) (SLit 48)));
   YP09.mkChunk 5 (CVal 1 (SAlu ALU_SRL (SOff 8 0) (SLit 40)));
   YP09.mkChunk 4 (CVal 1 (SAlu ALU_SRL (SOff 8 0) (SLit 32)))].

(* a one-byte chunk reads its value's low byte *)
Lemma fm_byte_chunk : forall E m h k e,
  YP09.chunk_ok tfibsegs E m h (YP09.mkChunk k (CVal 1 e)) ->
  mbyte tfibsegs m (h + k) = Some (Z_to_bv 8 (bv_unsigned (sv_denot E e))).
Proof.
intros E m h k e H.
destruct (H 0 ltac:(cbn; lia)) as (b0 & H1 & H2).
cbn [YP09.cbyte YP09.c_off YP09.c_val] in H1, H2.
injection H1 as <-.
rewrite Z.add_0_r in H2. rewrite H2. unfold YP09.byte_of_word. rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
Qed.

Lemma fm_srl_unsigned : forall E n s, bv_unsigned (ew E 8) = n -> 0 <= n < 2 ^ 64 -> 0 <= s < 64 ->
  bv_unsigned (sv_denot E (SAlu ALU_SRL (SOff 8 0) (SLit s))) = Z.shiftr n s.
Proof.
intros E n s Hn Hr Hs. cbn [sv_denot]. rewrite alu64_unsigned. cbn [zalu_raw].
rewrite !Z_to_bv_unsigned. rewrite Hn, Z.add_0_r.
assert (W1 : bv_wrap 64 n = n) by (apply bv_wrap_small; change (bv_modulus 64) with (2 ^ 64); lia).
assert (W2 : bv_wrap 64 s = s) by (apply bv_wrap_small; change (bv_modulus 64) with (2 ^ 64); lia).
rewrite W1, W2.
assert (L : Z.land s 63 = s)
  by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; apply Z.mod_small; change (2 ^ 6) with 64; lia).
rewrite L.
assert (S0 : 0 <= Z.shiftr n s <= n).
{ split; [apply Z.shiftr_nonneg; lia|]. rewrite Z.shiftr_div_pow2 by lia.
  apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|].
  pose proof (Z.pow_pos_nonneg 2 s ltac:(lia) ltac:(lia)). nia. }
apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

(* the head's 8 one-byte chunks hold n, little-endian *)
Lemma fm_head_val : forall E m h n,
  bv_unsigned (ew E 8) = n -> 0 <= n < 2 ^ 64 ->
  Forall (YP09.chunk_ok tfibsegs E m h) fm_head_cs -> val_mem tfibsegs m h 8 n.
Proof.
intros E m h n Hn Hr H k Hk.
rewrite (le_byte_small n 8 k ltac:(change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); lia) Hk).
unfold fm_head_cs in H.
pose proof (Forall_inv H) as Hc3. apply Forall_inv_tail in H.
pose proof (Forall_inv H) as Hc2. apply Forall_inv_tail in H.
pose proof (Forall_inv H) as Hc1. apply Forall_inv_tail in H.
pose proof (Forall_inv H) as Hc0. apply Forall_inv_tail in H.
pose proof (Forall_inv H) as Hc7. apply Forall_inv_tail in H.
pose proof (Forall_inv H) as Hc6. apply Forall_inv_tail in H.
pose proof (Forall_inv H) as Hc5. apply Forall_inv_tail in H.
pose proof (Forall_inv H) as Hc4.
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [..| lia].
all: first
  [ etransitivity; [exact (fm_byte_chunk E m h _ _ Hc0) |]
  | etransitivity; [exact (fm_byte_chunk E m h _ _ Hc1) |]
  | etransitivity; [exact (fm_byte_chunk E m h _ _ Hc2) |]
  | etransitivity; [exact (fm_byte_chunk E m h _ _ Hc3) |]
  | etransitivity; [exact (fm_byte_chunk E m h _ _ Hc4) |]
  | etransitivity; [exact (fm_byte_chunk E m h _ _ Hc5) |]
  | etransitivity; [exact (fm_byte_chunk E m h _ _ Hc6) |]
  | etransitivity; [exact (fm_byte_chunk E m h _ _ Hc7) |] ].
all: f_equal; f_equal.
all: first
  [ solve [apply (fm_srl_unsigned E n); [exact Hn | exact Hr | lia]]
  | solve [change (8 * Z.of_nat 0) with 0; rewrite Z.shiftr_0_r; cbn [sv_denot]; rewrite Z_to_bv_unsigned, Hn, Z.add_0_r;
           apply bv_wrap_small; change (bv_modulus 64) with (2 ^ 64); lia] ].
Qed.

(* the state resumed after the malloc call (0x8290c), under the env Ereg regs2 (fs_extraT ++ xs) with
   xs = [cnt + 1; fail; live; peak; ra0; s0_0; s1_0; s2_0] (atoms 33..40): the frame's four saved registers as atoms
   37..40, the four statics (atoms 33..36), the new block's 8-byte head as a writable region based at a0 = b (atom 10);
   gf gives the token run of own()'s two inline shadow checks its ranges: atom 18 (s2) is the shadow base exactly, atom 10
   is a 16-aligned block address below alloc_ceiling's bound (MEASURED: without them sh_static_ok is false) *)
Definition fm_cs : list YP09.chunk :=
  [YP09.mkChunk 0 (CVal 8 (SOff 40 0)); YP09.mkChunk 8 (CVal 8 (SOff 39 0));
   YP09.mkChunk 16 (CVal 8 (SOff 38 0)); YP09.mkChunk 24 (CVal 8 (SOff 37 0))].
Definition fm_rsA : list YP09.region := fs_pstat_regions ++ [fs_head_region 10 8 []].
Definition fm_gf : list (nat * afact) := [(18%nat, mkAF 0x7fff8000 0x7fff8000 0); (10%nat, mkAF 4096 0x7fffff800000 4)].

Lemma fm_pstat_bounds : forall a, inFP FS_PSTAT_FP a ->
  (G_FAIL <= a < G_FAIL + 8) \/ (G_LIVE <= a < G_LIVE + 8) \/ (G_PEAK <= a < G_PEAK + 8) \/ (G_COUNT <= a < G_COUNT + 8).
Proof.
intros a (r & Hr & Ha). unfold FS_PSTAT_FP in Hr. unfold G_FAIL, G_LIVE, G_PEAK, G_COUNT.
repeat (destruct Hr as [<- | Hr]; [cbn [fst snd] in Ha; lia|]). destruct Hr.
Qed.

(* fs_glob is kept when the statics' bytes are (across a call, a world change included) *)
Lemma fm_glob_keep : forall (W W' : world tfibsegs) m m' live peak cnt fail,
  fs_glob tfibsegs W m live peak cnt fail ->
  (forall a, inFP FS_PSTAT_FP a -> mbyte tfibsegs (mrestrict (w_H W') m') a = mbyte tfibsegs (mrestrict (w_H W) m) a) ->
  fs_glob tfibsegs W' m' live peak cnt fail.
Proof.
intros W W' m m' live peak cnt fail (G1 & G2 & G3 & G4 & GR) He.
assert (V : forall g v, In (g, g + 8) FS_PSTAT_FP -> val_mem tfibsegs (mrestrict (w_H W) m) g 8 v ->
  val_mem tfibsegs (mrestrict (w_H W') m') g 8 v).
{ intros g v Hg Hv k Hk. rewrite He; [exact (Hv k Hk)|]. apply (inFP_FS_PSTAT_FP g Hg). lia. }
split; [apply (V G_LIVE); [vm_compute; tauto | exact G1]|].
split; [apply (V G_PEAK); [vm_compute; tauto | exact G2]|].
split; [apply (V G_COUNT); [vm_compute; tauto | exact G3]|].
split; [apply (V G_FAIL); [vm_compute; tauto | exact G4]|].
exact GR.
Qed.

(* the resumed states' extra atoms 33..40 (see fm_cs) *)
Definition fm_xs (regs : bvmap 5 word) (cnt fail live peak : Z) : list word :=
  fs_pstat_xs (cnt + 1) fail live peak ++ [getr regs 1; getr regs 8; getr regs 9; getr regs 18].
(* what the callee-saved registers hold at fuzz_malloc's `ret`: sp back up by the frame, s0 / s1 / s2 reloaded from the
   frame's atoms 38..40, the rest untouched *)
Definition fm_expect (r : bv 5) : sv :=
  match bv_unsigned r with
  | 2 => SOff 2 32 | 8 => SOff 38 0 | 9 => SOff 39 0 | 18 => SOff 40 0
  | z => SOff (Z.to_nat z) 0
  end.

(* bytes no region of a run writes keep their value across the run (frame_of) *)
Lemma fm_val_mem_frame : forall E rs (H : word -> bool) m m' a (k : nat) v,
  frame_of E rs m m' -> (forall i, (i < k)%nat -> ~ in_wrange E rs (a + Z.of_nat i)) -> 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  val_mem tfibsegs (mrestrict H m) a k v -> val_mem tfibsegs (mrestrict H m') a k v.
Proof.
intros E rs H m m' a k v HF Hn Ha Hk Hv i Hi. rewrite <- (Hv i Hi).
apply (mbyte_of_aview tfibsegs). apply (aview_at tfibsegs). apply HF. rewrite (wz (a + Z.of_nat i) ltac:(lia)). exact (Hn i Hi).
Qed.

Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* as Section n *)
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis SHS : FsShadowSyms B.
Let FS_GOT_SHADOW : as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address := proj1 SHS.
Let FS_SHADOW_CELL : as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address := proj2 SHS.
(* fs's B is TfibB (A/AF0m.v TfibSyms): its code pcs (Tfib_code), its trace universe's laws; owner the S0 start-up layer *)
Hypothesis HB : TfibSyms B.
(* the donor allocator walks' errno / UNIV0 environment (Reusable/YCbq.v api_env); owner RELOC *)
Hypothesis FS_ENV : api_env tfibsegs B.
(* __wrap_malloc in ARU form (FSupoisonU.amalloc_realizesU, FSH_Rt.FsRt.fr_malloc's second conjunct); owner the shared
   runtime (a Theorem Labs lane's U twin of the cgif core AF0w, SHARED-WALKS row 'Allocate / Deallocate') *)
Hypothesis FS_AMALLOC_AU : FSupoisonU.amalloc_realizesU tfibsegs B.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let ML : model_laws (as_universe B) := model_laws_ok (as_universe B) (ts_universe B HB).

(* below the shadow (the image, the heap) the unpoisoned reading is the machine's *)
Lemma fm_aview_low : forall ly S U (W : world tfibsegs) mem md a, ARU tfibsegs B ly S U W mem md -> 0 <= a < SHADOW_OFF ->
  aview tfibsegs (w_H W) (unpoison U mem) a = aview tfibsegs (w_H W) mem a.
Proof.
intros ly S U W mem md a H Ha. apply (aview_at tfibsegs).
apply (fs_head_app_view B ly S U W mem md a H); [unfold SHADOW_OFF in *; lia | left; lia].
Qed.
(* the statics are kept across an allocator call (acall_kept's image clause, read without unpoison) *)
Lemma fm_glob_acall : forall lyc Sc U (W W2 : world tfibsegs) memc mem2 mdc ly2 S2 md2 slo shi Ex live peak cnt fail,
  ARU tfibsegs B lyc Sc U W memc mdc -> ARU tfibsegs B ly2 S2 U W2 mem2 md2 ->
  acall_kept tfibsegs B lyc Sc W (unpoison U memc) W2 (unpoison U mem2) slo shi Ex ->
  fs_glob tfibsegs W memc live peak cnt fail -> fs_glob tfibsegs W2 mem2 live peak cnt fail.
Proof.
intros lyc Sc U W W2 memc mem2 mdc ly2 S2 md2 slo shi Ex live peak cnt fail H1 H2 (_ & _ & HKimg & _) G.
apply (fm_glob_keep W W2 memc mem2 _ _ _ _ G). intros a Ha.
pose proof (fm_pstat_bounds a Ha) as Hb.
assert (Hlo : 0 <= a < SHADOW_OFF) by (unfold G_FAIL, G_LIVE, G_PEAK, G_COUNT, SHADOW_OFF in *; lia).
apply (mbyte_of_aview tfibsegs).
rewrite <- (fm_aview_low ly2 S2 U W2 mem2 md2 a H2 Hlo), <- (fm_aview_low lyc Sc U W memc mdc a H1 Hlo).
apply HKimg; [exact (fs_pstat_img a Ha) | exact (fs_pstat_not_owned tfibsegs B _ _ _ _ _ _ _ IMG a Ha) |].
rewrite (ts_errno B HB). unfold TFIB_ERRNO, G_FAIL, G_LIVE, G_PEAK, G_COUNT in *. lia.
Qed.

(* across a poison / unpoison call: an application byte away from the call's stack window keeps its machine value
   (the call's aview clause read without the user poison, which application bytes do not carry) *)
Lemma fm_keep_app : forall ly S U U' (W : world tfibsegs) memT mem2 md md2 sp a,
  ARU tfibsegs B ly S U W memT md -> ARU tfibsegs B ly S U' W mem2 md2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - PO_WIN <= a < sp) ->
     aview tfibsegs (w_H W) (unpoison U' mem2) a = aview tfibsegs (w_H W) (unpoison U memT) a) ->
  0 <= a < 2 ^ 64 -> a < SHADOW_OFF \/ kHighMemBeg <= a -> ~ (sp - PO_WIN <= a < sp) ->
  mbyte tfibsegs (mrestrict (w_H W) mem2) a = mbyte tfibsegs (mrestrict (w_H W) memT) a.
Proof.
intros ly S U U' W memT mem2 md md2 sp a H1 H2 HK Ha Happ Hw.
apply (mbyte_of_aview tfibsegs).
assert (V1 : aview tfibsegs (w_H W) (unpoison U' mem2) a = aview tfibsegs (w_H W) mem2 a)
  by (apply (aview_at tfibsegs); exact (fs_head_app_view B ly S U' W mem2 md2 a H2 Ha Happ)).
assert (V2 : aview tfibsegs (w_H W) (unpoison U memT) a = aview tfibsegs (w_H W) memT a)
  by (apply (aview_at tfibsegs); exact (fs_head_app_view B ly S U W memT md a H1 Ha Happ)).
rewrite <- V1, <- V2. exact (HK a Ha Hw).
Qed.

(* awr_ok at the state resumed after malloc (fss_retT with rs = fm_rsA): FSW_statics_awr.fsw_awr_retTS for the frame,
   cells and statics, and the head region's window [b, b + 8): a byte of the block malloc made in this walk, so
   awr_byte0's temporary-block arm (in a block of blc not in the entry's bl0) *)
Lemma fm_awr_retA : forall E (r STK sp0 b m : Z) cs gf FP ly S ly2 S2 own fr0,
  bv_unsigned (ew E 2) = sp0 - 32 -> 32 <= STK -> bv_unsigned (ew E 10) = b ->
  (forall a, inFP FS_PSTAT_FP a -> inFP FP a) ->
  In (b, m) (ablocks B ly2 S2) -> ~ In (b, m) (ablocks B ly S) -> 8 <= req_size m ->
  awr_ok tfibsegs B E (ss_mem (fss_retT r 32 cs fm_rsA gf)) STK sp0 FP (ablocks B ly S) (ablocks B ly2 S2) ly2 own fr0.
Proof.
intros E r STK sp0 b m cs gf FP ly S ly2 S2 own fr0 E2 Hf E10 HFP Hin Hfr Hm a (rg & Hr & Ha).
change (In rg (fsT_ret_regions 32 cs (fs_pstat_regions ++ [fs_head_region 10 8 []]))) in Hr.
unfold fsT_ret_regions in Hr. rewrite app_assoc in Hr. apply in_app_or in Hr as [Hr | [<- | []]].
- apply (fsw_awr_retTS B IMG E r 32 STK sp0 cs gf FP (ablocks B ly S) (ablocks B ly2 S2) ly2 own fr0 E2 ltac:(lia) HFP a).
  exists rg. split; [exact Hr | exact Ha].
- cbn [fs_head_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite E10 in Ha.
  left. right. right. left. exists b, m. split; [exact Hin|]. split; [exact Hfr | lia].
Qed.

(* ---- the tail after own()'s poison call: from the state resumed at 0x82980 (fss_retT, rs = the statics) to the return.
   0x82980..0x82994: g_live := live + n; `bgeu peak, live + n` 0x82998: taken skips `g_peak := live + n`; both arms
   a0 = b + 16, epilogue, ret 0x829c0. fpostU with the spec's post at res = b + 16. ---- *)
Lemma fm_tail : forall ly S U (W : world tfibsegs) regs mem md n live peak cnt fail ly2 S2 W2 regs3 mem3 md3 b,
  st_ok tfibsegs (Ereg regs3 (fs_extraT ++ fm_xs regs cnt fail live peak))
    (fss_retT A_fuzz_malloc_ra_po 32 fm_cs fs_pstat_regions [])
    (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 A_fuzz_malloc_ra_po) mem3 (seg_rom tfibsegs))) ->
  ajournal tfibsegs B STK_fuzz_malloc (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md [] ly2 S2 W2
    (unpoison (U ++ [(b, HEAD)]) mem3) md3 1 ->
  ARU tfibsegs B ly2 S2 (U ++ [(b, HEAD)]) W2 mem3 md3 ->
  spZ regs3 = spZ regs - 32 -> getr regs3 8 = w64 n -> getr regs3 9 = w64 b ->
  (forall r, acallee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 ->
     getr regs3 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  YK0s.ret_ok (getr regs 1) -> 1 <= n -> live + n < 2 ^ 64 -> 0 <= live <= peak -> peak < 2 ^ 64 ->
  0 <= cnt + 1 < 2 ^ 64 -> 0 <= fail < 2 ^ 64 ->
  4096 <= b -> b mod 16 = 0 -> b + (n + HEAD) <= alloc_ceiling ->
  ablocks B ly2 S2 = ablocks B ly S ++ [(b, n + HEAD)] -> fs_heads B ly S U ->
  val_mem tfibsegs (mrestrict (w_H W2) mem3) b 8 n ->
  (forall g, In (g, g + 8) FS_PSTAT_FP -> b + 8 <= g \/ g + 8 <= b) ->
  SRr tfibsegs W2 (mkCfg (mkst regs3 (Z_to_bv 64 A_fuzz_malloc_ra_po) mem3 (seg_rom tfibsegs)) md3)
    (fun W' c' => exists res,
       apost_baseU tfibsegs B STK_fuzz_malloc FS_PSTAT_FP regs ly S W mem md 1 U (U ++ [(res - HEAD, HEAD)])
       (fun ly' S' W' regs' mem' md' =>
          getr regs' 10 = w64 res /\ 4096 + HEAD <= res /\
          ablocks B ly' S' = ablocks B ly S ++ [(res - HEAD, n + HEAD)] /\
          fs_heads B ly' S' (U ++ [(res - HEAD, HEAD)]) /\
          (0 < n -> fs_rblock tfibsegs B ly' S' W' mem' res n) /\
          range_addressable (aview tfibsegs (w_H W') mem') SHADOW_OFF res n /\
          fs_glob tfibsegs W' mem' (live + n) (Z.max peak (live + n)) (cnt + 1) fail) W' c').
Proof.
intros ly S U W regs mem md n live peak cnt fail ly2 S2 W2 regs3 mem3 md3 b HS6 HJ HARU Rsp3 R8 R9 Hkept Hra Hn1
  Hlv Hlp Hp64 Hc64 Hf64 Hb4096 Hb16 Hbceil Hbl FH Hval IS.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HstJ & _).
pose proof HstJ as (Hal16J & Hstk0J & HceilJ & HsloJ & HshiJ & H47J & HbotJ & Htop2J & HtopJ).
pose proof asan_consts as (C1 & _ & C3 & _).
assert (FM : STK_fuzz_malloc = 16416) by reflexivity.
set (E3 := Ereg regs3 (fs_extraT ++ fm_xs regs cnt fail live peak)) in HS6.
assert (E3_2 : bv_unsigned (ew E3 2) = spZ regs - 32)
  by (subst E3; rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl); unfold spZ in Rsp3; exact Rsp3).
assert (EX3 : forall j w, nth j (fs_extraT ++ fm_xs regs cnt fail live peak) (Z_to_bv 64 0) = w -> ew E3 (32 + j) = w)
  by (intros j w Hw; subst E3; rewrite ew_Ereg_extra; exact Hw).
assert (U3_8 : bv_unsigned (ew E3 8) = n)
  by (subst E3; rewrite (ew_Ereg_nat regs3 _ 8 8%bv eq_refl), R8; unfold w64; apply unsigned_lit_small; lia).
assert (U3_9 : bv_unsigned (ew E3 9) = b)
  by (subst E3; rewrite (ew_Ereg_nat regs3 _ 9 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; unfold HEAD in *; lia).
assert (E3_35 : ew E3 35 = Z_to_bv 64 live) by exact (EX3 3%nat _ eq_refl).
assert (E3_36 : ew E3 36 = Z_to_bv 64 peak) by exact (EX3 4%nat _ eq_refl).
assert (E3_37 : ew E3 37 = getr regs 1) by exact (EX3 5%nat _ eq_refl).
assert (E3_38 : ew E3 38 = getr regs 8) by exact (EX3 6%nat _ eq_refl).
assert (E3_39 : ew E3 39 = getr regs 9) by exact (EX3 7%nat _ eq_refl).
assert (E3_40 : ew E3 40 = getr regs 18) by exact (EX3 8%nat _ eq_refl).
assert (U3_35 : bv_unsigned (ew E3 35) = live) by (rewrite E3_35; apply unsigned_lit_small; lia).
assert (U3_36 : bv_unsigned (ew E3 36) = peak) by (rewrite E3_36; apply unsigned_lit_small; lia).
assert (Hnew : In (b, n + HEAD) (ablocks B ly2 S2)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
assert (Hrq : req_size (n + HEAD) = n + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (n + 16) 0); lia).
assert (FH2 : fs_heads B ly2 S2 (U ++ [(b, HEAD)]))
  by exact (fs_heads_snoc B ly S ly2 S2 U b (n + HEAD) FH
    (fun x Hx => ltac:(rewrite Hbl; apply in_or_app; left; exact Hx)) Hnew ltac:(rewrite Hrq; unfold HEAD; lia)).
(* the head's 8 bytes are written by no region of the tail's runs (they lie below the frame and off the statics) *)
pose proof (IS G_FAIL ltac:(vm_compute; tauto)) as I3. pose proof (IS G_LIVE ltac:(vm_compute; tauto)) as I4.
pose proof (IS G_PEAK ltac:(vm_compute; tauto)) as I5. pose proof (IS G_COUNT ltac:(vm_compute; tauto)) as I6.
assert (NW : forall rs, skeleton rs = skeleton (ss_mem (fss_retT A_fuzz_malloc_ra_po 32 fm_cs fs_pstat_regions [])) ->
  forall i, (i < 8)%nat -> ~ in_wrange E3 rs (b + Z.of_nat i)).
{ intros rs Hsk i Hi Hw. apply (in_wrange_skeleton E3 rs _ _ Hsk) in Hw. destruct Hw as (rg & Hr & Ha).
  unfold fss_retT, fsT_ret_regions, fs_pstat_regions in Hr. cbn [ss_mem app] in Hr.
  repeat (destruct Hr as [<- | Hr]).
  all: first
    [ solve [exact Hr]
    | solve [cbn [fstk_ret fs_got_region fs_bcell_region fs_pstat_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
             rewrite ?E3_2 in Ha; unfold G_FAIL, G_LIVE, G_PEAK, G_COUNT, xatom, HEAD in *; lia] ]. }
assert (A3 : forall ss, skeleton (ss_mem ss) = skeleton (ss_mem (fss_retT A_fuzz_malloc_ra_po 32 fm_cs fs_pstat_regions [])) ->
  awr_ok tfibsegs B E3 (ss_mem ss) STK_fuzz_malloc (spZ regs) FS_PSTAT_FP (ablocks B ly S) (ablocks B ly2 S2) ly2 []
    (frames S))
  by (intros ss Hsk; eapply fm_awr_skel; [exact Hsk | exact (fsw_awr_retTS B IMG E3 A_fuzz_malloc_ra_po 32 STK_fuzz_malloc
    (spZ regs) fm_cs [] FS_PSTAT_FP _ _ ly2 [] (frames S) E3_2 ltac:(rewrite FM; lia) (fun a H => H))]).
assert (ADD : sv_denot E3 (SAlu ALU_ADD (SOff 8 0) (SOff 35 0)) = Z_to_bv 64 (live + n)).
{ apply bv_eq. change (bv_unsigned (sv_denot E3 (SAlu ALU_ADD (SOff 8 0) (SOff 35 0))))
    with (YP0e.U E3 (SAlu ALU_ADD (SOff 8 0) (SOff 35 0))).
  rewrite U_add_off_atom; rewrite ?U3_8, ?U3_35; [rewrite unsigned_lit_small by lia; lia | unfold M64; lia | unfold M64; lia]. }
(* 0x82980..0x82994: g_live := live + n; stops at `bgeu a3, s0` *)
fsw_aj_runU tbl_fm_ok HS6 HJ HARU.
{ apply A3. reflexivity. }
pose proof HF as HF1. clear HFr HG HF.
(* the post at res = b + 16 *)
eapply SRr_mono.
2: { intros W' c' _ HQ. exists (b + HEAD). rewrite Z.add_simpl_r. exact HQ. }
eapply SRr_sym_branch with (c := BC_GEU) (a := SOff 36 0) (b := SAlu ALU_ADD (SOff 8 0) (SOff 35 0)) (1 := HS6).
all: intros Hbr HS7; clear HS6.
all: rewrite branch_geu_U, (U_off E3 36 0 ltac:(rewrite U3_36; unfold M64; lia)), U3_36 in Hbr.
all: change (YP0e.U E3 (SAlu ALU_ADD (SOff 8 0) (SOff 35 0))) with (bv_unsigned (sv_denot E3 (SAlu ALU_ADD (SOff 8 0) (SOff 35 0)))) in Hbr.
all: rewrite ADD, unsigned_lit_small in Hbr by lia.
all: fsw_aj_runU tbl_fm_ok HS7 HJ HARU.
all: try (apply A3; lazymatch goal with |- skeleton _ = skeleton _ => vm_compute; reflexivity end).
all: pose proof HF as HF2; clear HFr HG HF.
all: pose proof HS7 as HS7c; destruct HS7c as (_ & _ & _ & _ & _ & _ & _ & HMf & _).
all: rreg HS7 (1%bv : bv 5) R1f; rreg HS7 (10%bv : bv 5) R10f.
all: rewrite ?wvb_collapse in HJ, HARU.
all: unfold apost_baseU.
all: eapply (fsw_retU B tbl_fm tbl_fm_ok).
all: first
  [ solve [exact HS7] | solve [exact HJ] | solve [exact HARU]
  | solve [lazymatch goal with |- ss_resv _ = None => reflexivity end]
  | solve [lazymatch goal with |- clookup _ _ = Some _ => vm_compute; reflexivity end]
  | solve [lazymatch goal with |- v_jalr _ _ = _ =>
             rewrite R1f, ?fsw_SOff0, E3_37; exact Hra end]
  | solve [lazymatch goal with |- aregs_preserved _ _ =>
             apply (fsw_preserved _ E3 _ _ regs fm_expect HS7);
             [ lazymatch goal with |- forallb _ _ = true => vm_compute; reflexivity end
             | intros r Hr; cbv [CALLEE_SAVED In] in Hr;
               repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
               lazymatch goal with |- sv_denot _ (fm_expect ?q) = _ =>
                 let e := eval vm_compute in (fm_expect q) in change (fm_expect q) with e end;
               first
               [ apply fsw_sp_back; exact E3_2
               | rewrite fsw_SOff0; first [exact E3_38 | exact E3_39 | exact E3_40]
               | rewrite fsw_SOff0; subst E3;
                 lazymatch goal with |- ew _ ?k = YK11.getr _ ?q =>
                   rewrite (ew_Ereg_nat regs3 _ k q eq_refl);
                   let z := eval vm_compute in (bv_unsigned q) in
                   pose proof (Hkept z ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hk;
                   exact Hk end ] ] end]
  | idtac ].
(* left: the post Q of each arm *)
all: intros mat2; cbv beta.
all: split; [apply bv_eq; rewrite R10f; rewrite ?denot_SOff, ?U3_9; unfold w64, HEAD; rewrite ?unsigned_lit_small by lia;
             first [reflexivity | lia | (apply zcanon_id; unfold M64; lia)]|].
all: split; [unfold HEAD; lia|].
all: split; [exact Hbl|].
all: split; [exact FH2|].
all: split; [intros _; unfold fs_rblock; rewrite Z.add_simpl_r; split; [exact Hnew|];
             split; [unfold HEAD; rewrite Z.add_mod, Hb16 by lia; reflexivity|]; split; [lia|];
             apply (fm_val_mem_frame E3 _ (w_H W2) _ _ b 8 n HF2);
             [ apply NW; lazymatch goal with |- skeleton _ = skeleton _ => vm_compute; reflexivity end
             | unfold HEAD in *; lia | unfold HEAD in *; lia |];
             apply (fm_val_mem_frame E3 _ (w_H W2) mem3 _ b 8 n HF1);
             [ apply NW; reflexivity | unfold HEAD in *; lia | unfold HEAD in *; lia | exact Hval ]|].
all: split; [exact (fsw_block_body_addressable B ly2 S2 (U ++ [(b, HEAD)]) W2 _ _ b (n + HEAD) (b + HEAD) n HARU FH2 Hnew
               ltac:(unfold HEAD; lia) ltac:(lia) ltac:(rewrite Hrq; unfold HEAD; lia))|].
- (* taken: peak >= live + n, g_peak kept *)
  rewrite Z.max_l by (apply negb_true_iff, Z.ltb_ge in Hbr; lia).
  apply (fs_glob_of_TS E3 W2 _ _ (live + n) peak (cnt + 1) fail (SAlu ALU_ADD (SOff 8 0) (SOff 35 0)) (SOff 36 0)
    (SOff 33 0) (SOff 34 0) HMf).
  all: first
    [ solve [lazymatch goal with |- fs_pstat_find _ _ = Some _ => vm_compute; reflexivity end]
    | solve [exact ADD]
    | solve [rewrite fsw_SOff0; exact (EX3 4%nat _ eq_refl)]
    | solve [rewrite fsw_SOff0; exact (EX3 1%nat _ eq_refl)]
    | solve [rewrite fsw_SOff0; exact (EX3 2%nat _ eq_refl)]
    | solve [apply negb_true_iff, Z.ltb_ge in Hbr; lia]
    | solve [lia] ].
- (* not taken: peak < live + n, g_peak := live + n *)
  rewrite Z.max_r by (apply negb_false_iff, Z.ltb_lt in Hbr; lia).
  apply (fs_glob_of_TS E3 W2 _ _ (live + n) (live + n) (cnt + 1) fail (SAlu ALU_ADD (SOff 8 0) (SOff 35 0))
    (SAlu ALU_ADD (SOff 8 0) (SOff 35 0)) (SOff 33 0) (SOff 34 0) HMf).
  all: first
    [ solve [lazymatch goal with |- fs_pstat_find _ _ = Some _ => vm_compute; reflexivity end]
    | solve [exact ADD]
    | solve [rewrite fsw_SOff0; exact (EX3 1%nat _ eq_refl)]
    | solve [rewrite fsw_SOff0; exact (EX3 2%nat _ eq_refl)]
    | solve [lia] ].
Qed.

Lemma fm_malloc_arm : forall ly S U (W : world tfibsegs) regs mem md ch n live peak cnt fail,
  fpreU tfibsegs B STK_fuzz_malloc ly S U W regs mem md ch -> fs_heads B ly S U ->
  getr regs 10 = w64 n -> 1 <= n -> n + HEAD < MALLOC_MAX ->
  fs_glob tfibsegs W mem live peak cnt fail -> live + n < 2 ^ 64 -> cnt + 1 < 2 ^ 64 ->
  st_nev S + 1 <= EV_MAX -> blocks_bytes S + (n + HEAD) <= LIVE_MAX -> cnt <> fail ->
  SRr tfibsegs W (cfg_at tfibsegs A_fuzz_malloc regs mem md)
    (fun W' c' => exists res,
       apost_baseU tfibsegs B STK_fuzz_malloc FS_PSTAT_FP regs ly S W mem md 1 U (U ++ [(res - HEAD, HEAD)])
       (fun ly' S' W' regs' mem' md' =>
          getr regs' 10 = w64 res /\ 4096 + HEAD <= res /\
          ablocks B ly' S' = ablocks B ly S ++ [(res - HEAD, n + HEAD)] /\
          fs_heads B ly' S' (U ++ [(res - HEAD, HEAD)]) /\
          (0 < n -> fs_rblock tfibsegs B ly' S' W' mem' res n) /\
          range_addressable (aview tfibsegs (w_H W') mem') SHADOW_OFF res n /\
          fs_glob tfibsegs W' mem' (live + n) (Z.max peak (live + n)) (cnt + 1) fail) W' c').
Proof.
intros ly S U W regs mem md ch n live peak cnt fail HPRE FH H10 Hn1 Hn2 HGL Hlv Hcn Hev Hbb Hcf.
pose proof HPRE as (HAP & HRO).
pose proof (fsw_ARU B STK_fuzz_malloc ly S U W regs mem md ch HAP) as HARU.
pose proof HAP as (HAN & _ & _).
pose proof HAN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof HGL as (_ & _ & _ & _ & Hlp & Hp64 & Hc64 & Hf64).
pose proof (fsw_sp B STK_fuzz_malloc ly S U W regs mem md ch HAP) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _ & C3 & _).
assert (FM : STK_fuzz_malloc = 16416) by reflexivity.
assert (Hn64 : 0 <= n < 2 ^ 64) by (unfold MALLOC_MAX, HEAD in *; lia).
pose proof (fsw_entryTS B STK_fuzz_malloc 32 ly S U W regs mem md ch A_fuzz_malloc live peak cnt fail
  FS_GOT_SHADOW FS_SHADOW_CELL HAP ltac:(rewrite FM; lia) ltac:(vm_compute; reflexivity) HGL) as HS.
pose proof (ajournal_init tfibsegs B STK_fuzz_malloc FS_PSTAT_FP ly S W regs (unpoison U mem) md ch HAN) as HJ.
set (E := Ereg regs (fs_extraTS cnt fail live peak)) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 n) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (EX : forall j v, (j < 5)%nat -> nth j (fs_extraTS cnt fail live peak) (Z_to_bv 64 0) = Z_to_bv 64 v ->
  ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj Hv; subst E; rewrite ew_Ereg_extra; exact Hv).
assert (A0 : forall pc f FPx bl0 blc lyx own fr0, (forall a, inFP FS_PSTAT_FP a -> inFP FPx a) -> 0 <= f <= STK_fuzz_malloc ->
  awr_ok tfibsegs B E (ss_mem (fss0TS pc f)) STK_fuzz_malloc (spZ regs) FPx bl0 blc lyx own fr0)
  by (intros pc f FPx bl0 blc lyx own fr0 HFP Hf; exact (fsw_awr_TS B IMG E pc f STK_fuzz_malloc (spZ regs) FPx bl0 blc lyx own fr0 Usp ltac:(lia) HFP)).
unfold cfg_at. change (w64 A_fuzz_malloc) with (Z_to_bv 64 A_fuzz_malloc).
(* 0x828ac..0x828e4 as in fm_null_arm; stops at `bne a3, a4` *)
fsw_aj_runU tbl_fm_ok HS HJ HARU.
{ exact (A0 A_fuzz_malloc 32 FS_PSTAT_FP _ _ _ _ _ (fun a H => H) ltac:(lia)). }
clear HF HFr HG.
eapply SRr_sym_branch with (c := BC_NE) (a := SOff 33 0) (b := SOff 34 0) (1 := HS).
2: { (* not taken: cnt = fail, refuted *)
  intros Hb _. exfalso.
  rewrite branch_ne_U, (U_atom E 33 cnt (EX 1%nat cnt ltac:(lia) eq_refl) Hc64),
    (U_atom E 34 fail (EX 2%nat fail ltac:(lia) eq_refl) Hf64) in Hb.
  apply negb_false_iff, Z.eqb_eq in Hb. exact (Hcf Hb). }
intros _ HS2. clear HS.
(* 0x828fc: a0 = -17; stops at `bltu a0, s0` *)
fsw_aj_runU tbl_fm_ok HS2 HJ HARU.
{ eapply fm_awr_skel; [| exact (A0 A_fuzz_malloc 32 FS_PSTAT_FP _ _ _ _ _ (fun a H => H) ltac:(lia))].
  lazymatch goal with |- skeleton _ = skeleton _ => vm_compute; reflexivity end. }
clear HF HFr HG.
eapply SRr_sym_branch with (c := BC_LTU) (a := SLit 18446744073709551599) (b := SOff 10 0) (1 := HS2).
1: { (* taken: n > 2^64 - 17, refuted *)
  intros Hb _. exfalso.
  rewrite branch_ltu_U, (U_lit E 18446744073709551599 ltac:(lia)), (U_atom E 10 n E10 Hn64) in Hb.
  apply Z.ltb_lt in Hb. unfold MALLOC_MAX, HEAD in *. lia. }
intros _ HS3. clear HS2.
(* 0x82904: a0 = n + 16; `jal __wrap_malloc`: stops at the fetch of 0x53074 *)
fsw_aj_runU tbl_fm_ok HS3 HJ HARU.
{ eapply fm_awr_skel; [| exact (A0 A_fuzz_malloc 32 FS_PSTAT_FP _ _ _ _ _ (fun a H => H) ltac:(lia))].
  lazymatch goal with |- skeleton _ = skeleton _ => vm_compute; reflexivity end. }
clear HF HFr HG.
rewrite ?wvb_collapse in HJ, HARU.
(* ---- at the `jal __wrap_malloc` target: register facts, the statics, the call ---- *)
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms1 HS3 eq_refl) as Hshape.
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by exact (EX 0%nat SHADOW_OFF ltac:(lia) eq_refl).
assert (E33 : ew E 33 = Z_to_bv 64 cnt) by exact (EX 1%nat cnt ltac:(lia) eq_refl).
assert (U10 : bv_unsigned (ew E 10) = n) by (rewrite E10; apply unsigned_lit_small; lia).
assert (R1 : getr (ms_regs ms1) 1 = Z_to_bv 64 A_fuzz_malloc_ra)
  by exact (fsw_reg_lit _ E _ ms1 1%bv 534796 HS3 ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (R10 : getr (ms_regs ms1) 10 = w64 (n + 16)).
{ pose proof (fsw_reg_off _ E _ ms1 10%bv 10 16 n HS3 ltac:(vm_compute; reflexivity) U10
    ltac:(unfold MALLOC_MAX, HEAD in *; lia)) as H.
  unfold w64. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned. }
assert (Rsp : spZ (ms_regs ms1) = spZ regs - 32).
{ unfold spZ at 1. exact (fsw_reg_off _ E _ ms1 2%bv 2 (-32) (spZ regs) HS3 ltac:(vm_compute; reflexivity) Usp
    ltac:(unfold spZ in *; pose proof (bv_unsigned_in_range _ (getr regs 2)); lia)). }
assert (R3 : getr (ms_regs ms1) 3 = getr regs 3)
  by exact (fsw_reg_atom (w_H W) regs _ _ ms1 3%bv 3%bv 3 HS3 ltac:(vm_compute; reflexivity) eq_refl).
assert (R4 : getr (ms_regs ms1) 4 = getr regs 4)
  by exact (fsw_reg_atom (w_H W) regs _ _ ms1 4%bv 4%bv 4 HS3 ltac:(vm_compute; reflexivity) eq_refl).
assert (R8 : getr (ms_regs ms1) 8 = getr regs 10)
  by exact (fsw_reg_atom (w_H W) regs _ _ ms1 8%bv 10%bv 10 HS3 ltac:(vm_compute; reflexivity) eq_refl).
assert (R9 : getr (ms_regs ms1) 9 = getr regs 9)
  by exact (fsw_reg_atom (w_H W) regs _ _ ms1 9%bv 9%bv 9 HS3 ltac:(vm_compute; reflexivity) eq_refl).
assert (R18 : bv_unsigned (getr (ms_regs ms1) 18) = SHADOW_OFF)
  by exact (fsw_reg_off _ E _ ms1 18%bv 32 0 SHADOW_OFF HS3 ltac:(vm_compute; reflexivity)
    ltac:(rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)).
pose proof HS3 as HS3c. destruct HS3c as (_ & _ & _ & _ & _ & _ & _ & HM3 & _).
(* the statics at the call: g_count = cnt + 1 (fs_glob read back from the symbolic memory) *)
assert (G1 : fs_glob tfibsegs W (ms_mem ms1) live peak (cnt + 1) fail).
{ apply (fs_glob_of_TS E W _ _ live peak (cnt + 1) fail (SOff 35 0) (SOff 36 0) (SOff 33 1) (SOff 34 0) HM3).
  all: first
    [ solve [lazymatch goal with |- fs_pstat_find _ _ = Some _ => vm_compute; reflexivity end]
    | solve [rewrite fsw_SOff0; exact (EX 3%nat live ltac:(lia) eq_refl)]
    | solve [rewrite fsw_SOff0; exact (EX 4%nat peak ltac:(lia) eq_refl)]
    | solve [rewrite fsw_SOff0; exact (EX 2%nat fail ltac:(lia) eq_refl)]
    | solve [lazymatch goal with |- sv_denot _ (SOff 33 1) = _ =>
               apply bv_eq; rewrite denot_SOff, E33; rewrite !unsigned_lit_small by lia;
               apply zcanon_id; unfold M64; lia end]
    | solve [lia] ]. }
rewrite Hshape.
replace (Z_to_bv 64 (ss_pc _)) with (Z_to_bv 64 (pc_wrap_malloc (as_code B))) by (rewrite (ts_code B HB); reflexivity).
eapply SRr_bind.
{ apply (fsw_aj_malloc04U_sub B FS_ENV ML FS_AMALLOC_AU W (ms_regs ms1) (ms_mem ms1) STK_fuzz_malloc (spZ regs)
    FS_PSTAT_FP ly S W mem md [] ly S U _ 0 (n + 16) (-32) (Z_to_bv 64 A_fuzz_malloc_ra) [] HJ HARU).
  all: first
    [ solve [exact R10] | solve [exact R1] | solve [rewrite R3; exact Hgp] | solve [rewrite R4; exact Htp]
    | solve [lazymatch goal with |- _ <= _ < MALLOC_MAX => unfold MALLOC_MAX, HEAD in *; lia end]
    | solve [lazymatch goal with |- blocks_bytes _ + _ <= _ => unfold HEAD in *; lia end]
    | solve [lazymatch goal with |- spZ _ = _ => rewrite Rsp; lia end]
    | solve [lazymatch goal with |- _ mod _ = _ => reflexivity end]
    | solve [lazymatch goal with |- ASTACK - _ <= _ => unfold ASTACK; rewrite FM; lia end]
    | solve [lazymatch goal with |- YK0s.ret_ok _ =>
               apply ret_ok_even; rewrite unsigned_lit_small by (unfold A_fuzz_malloc_ra; lia); reflexivity end]
    | solve [lazymatch goal with |- chain_pre _ _ _ _ =>
               unfold chain_pre; split;
               [ unfold raZ; rewrite R1, unsigned_lit_small by (unfold A_fuzz_malloc_ra; lia); unfold A_fuzz_malloc_ra; lia
               | destruct (frame0_ok ly (ms_regs ms1)); [|reflexivity];
                 replace (bad_next (spZ (ms_regs ms1)) (ly_top ly) (s0Z (ms_regs ms1))) with true; [reflexivity|];
                 symmetry; unfold bad_next; rewrite Rsp; unfold s0Z; rewrite R8, H10; unfold w64;
                 rewrite unsigned_lit_small by lia;
                 apply orb_true_iff; left; apply orb_true_iff; left; apply Z.leb_le;
                 unfold MALLOC_MAX, HEAD in *; lia ] end]
    | solve [lia] ]. }
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & b & -> & HARU2 & HJc & HP & Hb10 & Hfr & Hb4096 & Hbl & HK).
(* ---- resume at 0x8290c (FSW_K3.fsw_after_callFPU_args): frame chunks, statics, the new block's head, gf ---- *)
assert (Hnew : In (b, n + 16) (ablocks B ly2 S2)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
assert (Hrq : req_size (n + 16) = n + 16) by (unfold req_size; destruct (Z.eqb_spec (n + 16) 0); lia).
destruct (al_blocks _ _ LAWS ly2 S2 W2 (unpoison U mem2) md2 b (n + 16) (proj1 HARU2) Hnew) as (Hb16 & _ & Hbceil & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HstJ & _).
pose proof HstJ as (Hal16J & Hstk0J & HceilJ & HsloJ & HshiJ & H47J & HbotJ & Htop2J & HtopJ).
assert (Ub : bv_unsigned (getr regs2 10) = b) by (rewrite Hb10; unfold w64; apply unsigned_lit_small; lia).
assert (P18 : getr regs2 18 = getr (ms_regs ms1) 18) by exact (HP 18 ltac:(unfold acallee_saved; lia)).
assert (P2 : getr regs2 2 = getr (ms_regs ms1) 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
set (xs := fs_pstat_xs (cnt + 1) fail live peak ++ [getr regs 1; getr regs 8; getr regs 9; getr regs 18]).
set (E2 := Ereg regs2 (fs_extraT ++ xs)).
assert (E2_10 : bv_unsigned (ew E2 10) = b) by (subst E2; rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl); exact Ub).
assert (E2_18 : bv_unsigned (ew E2 18) = SHADOW_OFF)
  by (subst E2; rewrite (ew_Ereg_nat regs2 _ 18 18%bv eq_refl), P18; exact R18).
assert (E2_2 : bv_unsigned (ew E2 2) = spZ regs - 32)
  by (subst E2; rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), P2; unfold spZ in Rsp; exact Rsp).
assert (G2 : fs_glob tfibsegs W2 mem2 live peak (cnt + 1) fail)
  by exact (fm_glob_acall ly S U W W2 (ms_mem ms1) mem2 _ ly2 S2 md2 _ _ _ live peak (cnt + 1) fail HARU HARU2 HK G1).
replace (spZ regs + -32) with (spZ (ms_regs ms1)) in HJc by lia.
(* the frame's four saved registers, read at the call (the call state's frame region), moved to atoms 37..40 *)
destruct HM3 as (_ & HR3 & _).
cbn [ss_mem] in HR3.
pose proof (Forall_inv HR3) as (_ & _ & _ & HCK).
cbn [YP09.r_chunks YP09.r_base base_val] in HCK. rewrite Usp in HCK.
assert (FC : forall off e, In (YP09.mkChunk off (CVal 8 e))
    [YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
     YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] ->
  YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms1)) (spZ regs) (YP09.mkChunk off (CVal 8 e)))
  by (intros off e Hin; exact (proj1 (Forall_forall _ _) HCK _ Hin)).
assert (V : forall (k j : nat) (r : bv 5), nth j (fs_extraT ++ xs) (Z_to_bv 64 0) = getr regs r ->
    Z.of_nat k = bv_unsigned r -> sv_denot E (SOff k 0) = sv_denot E2 (SOff (32 + j) 0)).
{ intros k j r Hn Hk. rewrite !fsw_SOff0. subst E2. rewrite ew_Ereg_extra, Hn. subst E. exact (ew_Ereg_nat regs _ k r Hk). }
assert (Hck : Forall (YP09.chunk_ok tfibsegs E2 (mrestrict (w_H W) (ms_mem ms1)) (spZ regs - 32)) fm_cs).
{ unfold fm_cs. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
  - apply (fm_chunk_move E E2 _ (spZ regs) (spZ regs - 32) (-32) 0 8 (SOff 18 0) (SOff 40 0));
      [lia | exact (V 18%nat 8%nat 18%bv eq_refl eq_refl) | apply FC; cbn; tauto].
  - apply (fm_chunk_move E E2 _ (spZ regs) (spZ regs - 32) (-24) 8 8 (SOff 9 0) (SOff 39 0));
      [lia | exact (V 9%nat 7%nat 9%bv eq_refl eq_refl) | apply FC; cbn; tauto].
  - apply (fm_chunk_move E E2 _ (spZ regs) (spZ regs - 32) (-16) 16 8 (SOff 8 0) (SOff 38 0));
      [lia | exact (V 8%nat 6%nat 8%bv eq_refl eq_refl) | apply FC; cbn; tauto].
  - apply (fm_chunk_move E E2 _ (spZ regs) (spZ regs - 32) (-8) 24 8 (SOff 1 0) (SOff 37 0));
      [lia | exact (V 1%nat 5%nat 1%bv eq_refl eq_refl) | apply FC; cbn; tauto]. }
assert (Hrs : Forall (region_ok tfibsegs E2 (mrestrict (w_H W2) mem2)) fm_rsA).
{ unfold fm_rsA. apply Forall_app. split.
  - exact (fm_pstat_ok W2 regs2 mem2 live peak (cnt + 1) fail [getr regs 1; getr regs 8; getr regs 9; getr regs 18] G2).
  - constructor; [|constructor].
    apply (fs_head_region_ok B ly2 S2 U W2 mem2 md2 E2 10 b 8 [] b (n + 16) HARU2 Hnew);
      first [solve [exact E2_10] | solve [rewrite Hrq; lia] | solve [constructor] | solve [lia]]. }
assert (Himg : forall g, (forall x, g <= x < g + 8 -> in_img tfibsegs x) -> b + 8 <= g \/ g + 8 <= b)
  by (intros g Hg; exact (fs_head_img_apart B ly2 S2 W2 (unpoison U mem2) md2 b (n + 16) b g 8 (proj1 HARU2) Hnew
        ltac:(lia) ltac:(rewrite Hrq; lia) ltac:(lia) Hg)).
pose proof (Himg 0x9f6f0 (fun x Hx => fm_cells_img x (ex_intro _ (0x9f6f0, 0x9f6f8) (conj (or_introl eq_refl) Hx)))) as I1.
pose proof (Himg 0xa7f38 (fun x Hx => fm_cells_img x (ex_intro _ (0xa7f38, 0xa7f40) (conj (or_intror (or_introl eq_refl)) Hx)))) as I2.
assert (IS : forall g, In (g, g + 8) FS_PSTAT_FP -> b + 8 <= g \/ g + 8 <= b)
  by (intros g Hg; apply Himg; intros x Hx; exact (fs_pstat_img x (inFP_FS_PSTAT_FP g Hg x Hx))).
pose proof (IS G_FAIL ltac:(vm_compute; tauto)) as I3. pose proof (IS G_LIVE ltac:(vm_compute; tauto)) as I4.
pose proof (IS G_PEAK ltac:(vm_compute; tauto)) as I5. pose proof (IS G_COUNT ltac:(vm_compute; tauto)) as I6.
assert (Hpdj : pairwise_disjoint E2 (fsT_ret_regions 32 fm_cs fm_rsA)).
{ apply pairwise_disjoint_of_extents.
  unfold fsT_ret_regions, fm_rsA, fs_pstat_regions, fs_got_region, fs_bcell_region, fstk_ret, fs_pstat_region,
    fs_head_region, extent_of_region.
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E2_2, E2_10.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address,
    G_COUNT, G_FAIL, G_LIVE, G_PEAK in *.
  cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia | lia]. }
assert (Hgf : atoms_ok E2 fm_gf).
{ unfold fm_gf. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2_18, E2_10.
  repeat split; first [solve [exact I] | solve [unfold SHADOW_OFF; lia] | solve [change (2 ^ 0) with 1; apply Z.mod_1_r]
    | solve [change (2 ^ 4) with 16; exact Hb16] | solve [lia]]. }
destruct (fsw_after_callFPU_args B STK_fuzz_malloc (spZ regs) FS_PSTAT_FP [] ly S U W mem md W ly S U (ms_mem ms1) _ 0
  ASTACK [] 32 (ms_regs ms1) ly2 S2 U W2 regs2 mem2 md2 1 xs fm_cs fm_rsA fm_gf A_fuzz_malloc_ra
  FS_GOT_SHADOW FS_SHADOW_CELL HJ HARU HJc (fun a Ha => False_ind _ (inFP_nil a Ha))
  (proj1 (proj2 HARU2)) (proj2 (proj2 HARU2)) HP Rsp ltac:(lia) ltac:(unfold ASTACK; lia)
  ltac:(rewrite FM; unfold ASTACK; lia) eq_refl ltac:(vm_compute; reflexivity)
  ltac:(unfold fm_cs; repeat constructor; cbn; lia) Hck Hrs Hpdj Hgf) as (HJ2 & HARU3 & HS4).
fold E2 in HS4.
(* ---- 0x8290c `beqz a0` (not taken: a0 = b >= 4096); own()'s checks, n into the head, `jal poison` ---- *)
assert (Hfresh : ~ In (b, n + 16) (ablocks B ly S))
  by exact (fresh_of_snoc B ly2 S2 W2 (unpoison U mem2) md2 (ablocks B ly S) b (n + 16) (proj1 HARU2) Hbl
    ltac:(rewrite Hrq; lia)).
assert (A1 : forall ss, skeleton (ss_mem ss) = skeleton (ss_mem (fss_retT A_fuzz_malloc_ra 32 fm_cs fm_rsA fm_gf)) ->
  awr_ok tfibsegs B E2 (ss_mem ss) STK_fuzz_malloc (spZ regs) FS_PSTAT_FP (ablocks B ly S) (ablocks B ly2 S2) ly2 []
    (frames S))
  by (intros ss Hsk; eapply fm_awr_skel; [exact Hsk | exact (fm_awr_retA E2 A_fuzz_malloc_ra STK_fuzz_malloc (spZ regs) b
    (n + 16) fm_cs fm_gf FS_PSTAT_FP ly S ly2 S2 [] (frames S) E2_2 ltac:(rewrite FM; lia) E2_10 (fun a H => H) Hnew Hfresh
    ltac:(rewrite Hrq; lia))]).
fsw_aj_runU tbl_fm_ok HS4 HJ2 HARU3.
{ apply A1. lazymatch goal with |- skeleton _ = skeleton _ => vm_compute; reflexivity end. }
clear HF HFr HG.
eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 10 0) (b := SLit 0) (1 := HS4).
1: { intros Hb' _. exfalso. rewrite branch_eq_U, U_SOff, E2_10, Z.add_0_r, (U_lit E2 0 ltac:(lia)) in Hb'.
     rewrite zcanon_id in Hb' by (unfold M64; lia). apply Z.eqb_eq in Hb'. lia. }
intros _ HS5. clear HS4.
destruct (al_blocks _ _ LAWS ly2 S2 W2 (unpoison U mem2) md2 b (n + 16) (proj1 HARU2) Hnew) as (_ & _ & _ & Happ & _).
assert (DJ : Forall (zdisjoint (b, 16)) U)
  by (apply Forall_forall; exact (new_head_disjoint B ly S ly2 S2 W2 (unpoison U mem2) md2 U b (n + 16) (proj1 HARU2) FH
        (fun x Hx => ltac:(rewrite Hbl; apply in_or_app; left; exact Hx)) Hnew Hfresh ltac:(rewrite Hrq; lia))).
lazymatch type of HARU3 with ARU _ _ _ _ _ _ ?mm _ => set (MM := mm) in * end.
destruct (fs_head_shadow0 B ly2 S2 U W2 MM _ b (n + 16) HARU3 Hnew ltac:(rewrite Hrq; lia) DJ) as [Z0 Z1].
assert (SHOK : sh_ok tfibsegs (SOff 18 0) [YCbn.mkSHE 10 0 16] E2 (mrestrict (w_H W2) MM)).
{ constructor; [|constructor].
  apply (fs_head_shent (SOff 18 0) E2 W2 MM 10 b).
  all: first
    [ solve [exact Z0] | solve [exact Z1]
    | solve [lazymatch goal with |- U _ (SOff 10 0) = _ => rewrite U_SOff, E2_10, Z.add_0_r; apply zcanon_id; unfold M64; lia end]
    | solve [lazymatch goal with |- U _ (SOff 18 0) = _ =>
               rewrite U_SOff, E2_18, Z.add_0_r; apply zcanon_id; unfold M64, SHADOW_OFF; lia end]
    | solve [lazymatch goal with |- _ mod 8 = 0 =>
               apply Z.mod_divide; [lia|]; apply Z.mod_divide in Hb16; [|lia]; destruct Hb16 as [q Hq]; exists (2 * q); lia end]
    | solve [lazymatch goal with |- in_app _ _ => apply (in_app_sub b (req_size (n + 16)) b 16 Happ); rewrite ?Hrq; lia end] ]. }
fsw_aj_run_tokU tbl_fm_ok HS5 HJ2 HARU3 SHOK fs_Bspan.
{ apply A1. lazymatch goal with |- skeleton _ = skeleton _ => vm_compute; reflexivity end. }
(* ---- the poison call (own()'s `__asan_poison_memory_region(b, 16)`): FSW_poison_conv.fsw_poison16_atU over
   FSpoisonW.tfib_poison16; the new head is consed at the front, the statement appends it (Permutation_cons_append) ---- *)
pose proof HS5 as HS5c. destruct HS5c as (_ & _ & _ & _ & _ & _ & _ & HM5 & _).
pose proof HM5 as HM5c. destruct HM5c as (_ & HR5 & _). cbn [ss_mem] in HR5.
pose proof (Forall_inv HR5) as (_ & _ & _ & HCK5). cbn [YP09.r_chunks YP09.r_base base_val] in HCK5. rewrite E2_2 in HCK5.
pose proof HR5 as HRl. do 7 apply Forall_inv_tail in HRl.
pose proof (Forall_inv HRl) as (_ & _ & _ & HHC). cbn [YP09.r_chunks YP09.r_base base_val] in HHC. rewrite E2_10 in HHC.
clear HFr HG.
rewrite ?wvb_collapse in HJ2, HARU3 |- *.
assert (P3 : getr regs2 3 = getr (ms_regs ms1) 3) by exact (HP 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs2 4 = getr (ms_regs ms1) 4) by exact (HP 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8 = getr (ms_regs ms1) 8) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
pose proof alloc_ceiling_val as AC.
assert (E2_8 : bv_unsigned (ew E2 8) = n).
{ subst E2. rewrite (ew_Ereg_nat regs2 _ 8 8%bv eq_refl), P8, R8, H10. unfold w64. apply unsigned_lit_small. lia. }
assert (Hval0 : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms0)) b 8 n)
  by exact (fm_head_val E2 _ b n E2_8 Hn64 HHC).
assert (T1 : getr (ms_regs ms0) 1 = Z_to_bv 64 A_fuzz_malloc_ra_po)
  by exact (fsw_reg_lit _ E2 _ ms0 1%bv 534912 HS5 ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (T11 : getr (ms_regs ms0) 11 = w64 16)
  by exact (fsw_reg_lit _ E2 _ ms0 11%bv 16 HS5 ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (T10 : getr (ms_regs ms0) 10 = w64 b).
{ rewrite (fsw_reg_atom (w_H W2) regs2 (fs_extraT ++ xs) _ ms0 10%bv 10%bv 10 HS5 ltac:(vm_compute; reflexivity) eq_refl).
  exact Hb10. }
assert (T9 : getr (ms_regs ms0) 9 = w64 b).
{ rewrite (fsw_reg_atom (w_H W2) regs2 (fs_extraT ++ xs) _ ms0 9%bv 10%bv 10 HS5 ltac:(vm_compute; reflexivity) eq_refl).
  exact Hb10. }
assert (T8 : getr (ms_regs ms0) 8 = w64 n).
{ rewrite (fsw_reg_atom (w_H W2) regs2 (fs_extraT ++ xs) _ ms0 8%bv 8%bv 8 HS5 ltac:(vm_compute; reflexivity) eq_refl).
  rewrite P8, R8. exact H10. }
assert (T3 : getr (ms_regs ms0) 3 = w64 (as_gp B)).
{ rewrite (fsw_reg_atom (w_H W2) regs2 (fs_extraT ++ xs) _ ms0 3%bv 3%bv 3 HS5 ltac:(vm_compute; reflexivity) eq_refl).
  rewrite P3, R3. exact Hgp. }
assert (T4 : getr (ms_regs ms0) 4 = w64 (as_tp B)).
{ rewrite (fsw_reg_atom (w_H W2) regs2 (fs_extraT ++ xs) _ ms0 4%bv 4%bv 4 HS5 ltac:(vm_compute; reflexivity) eq_refl).
  rewrite P4, R4. exact Htp. }
assert (T2 : spZ (ms_regs ms0) = spZ regs + -32).
{ unfold spZ at 1.
  rewrite (fsw_reg_off _ E2 _ ms0 2%bv 2 0 (spZ regs - 32) HS5 ltac:(vm_compute; reflexivity) E2_2
    ltac:(rewrite FM in Hceil; lia)). lia. }
pose proof (st_ok_restrict_mkst tfibsegs (w_H W2) E2 _ ms0 HS5 eq_refl) as Hshape5.
rewrite Hshape5.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdg) ?Qg =>
  change (SRr tfibsegs W2 (cfg_at tfibsegs PO_ENTRY (ms_regs ms0) (ms_mem ms0) mdg) Qg) end.
eapply SRr_bind.
{ apply (fsw_poison16_atU B PO_ENTRY
    ltac:(first [ exact (tfib_poison16 B LAWS HB) | exact (tfib_poison16 B HB) | exact (tfib_poison16 B LAWS)
                | exact (tfib_poison16 B) ])
    STK_fuzz_malloc (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md [] ly2 S2 U (U ++ [(b, 16)]) W2 (ms_mem ms0) _
    (0 + 1) (ms_regs ms0) (-32) b b (n + 16) HJ2 HARU3).
  all: first
    [ solve [exact T2] | solve [exact T3] | solve [exact T4] | solve [exact T10] | solve [exact T11] | solve [exact Hnew]
    | solve [lazymatch goal with |- _ mod _ = _ => reflexivity end]
    | solve [lazymatch goal with |- ESTACK - _ <= _ => unfold ESTACK; rewrite FM; lia end]
    | solve [lazymatch goal with |- YK0s.ret_ok _ =>
               rewrite T1; apply ret_ok_even; rewrite unsigned_lit_small by (unfold A_fuzz_malloc_ra_po; lia); reflexivity end]
    | solve [apply (upoison_ok_new_head B ly2 S2 U b (n + 16) (proj1 (proj2 HARU3)) Hnew);
             first
             [ solve [lazymatch goal with |- _ mod 8 = 0 =>
                        apply Z.mod_divide; [lia|]; apply Z.mod_divide in Hb16; [|lia]; destruct Hb16 as [q Hq];
                        exists (2 * q); lia end]
             | solve [lazymatch goal with |- 16 <= 8 * (_ / 8) =>
                        rewrite Hrq; assert (2 <= (n + 16) / 8) by (apply Z.div_le_lower_bound; lia); lia end]
             | solve [intros r Hr; exact (proj1 (Forall_forall _ _) DJ r Hr)] ]]
    | solve [lazymatch goal with |- Permutation _ _ => apply Permutation_cons_append end]
    | solve [lazymatch goal with |- _ + _ < _ + req_size _ => rewrite Hrq; lia end]
    | solve [lazymatch goal with |- _ <= _ => lia end] ]. }
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HARU4 & HP3 & HFK & HAK).
rewrite T1.
(* ---- resume at 0x82980 with the frame and the statics (FSW_rres.fsw_resume_after_rtU_args), then fm_tail ---- *)
set (E3 := Ereg regs3 (fs_extraT ++ fm_xs regs cnt fail live peak)).
assert (Q2 : getr regs3 2 = getr (ms_regs ms0) 2) by exact (HP3 2 ltac:(unfold acallee_saved; lia)).
assert (Q8 : getr regs3 8 = getr (ms_regs ms0) 8) by exact (HP3 8 ltac:(unfold acallee_saved; lia)).
assert (Q9 : getr regs3 9 = getr (ms_regs ms0) 9) by exact (HP3 9 ltac:(unfold acallee_saved; lia)).
assert (E3_2 : bv_unsigned (ew E3 2) = spZ regs - 32)
  by (subst E3; rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl), Q2; unfold spZ in T2 |- *; lia).
assert (A23 : forall j, ew E2 (32 + j) = ew E3 (32 + j))
  by (intros j; subst E2 E3; rewrite !ew_Ereg_extra; reflexivity).
assert (EX2 : forall j w, nth j (fs_extraT ++ xs) (Z_to_bv 64 0) = w -> ew E2 (32 + j) = w)
  by (intros j w Hw; subst E2; rewrite ew_Ereg_extra; exact Hw).
(* the statics at the poison call, read back from the symbolic memory *)
assert (G0 : fs_glob tfibsegs W2 (ms_mem ms0) live peak (cnt + 1) fail).
{ apply (fs_glob_of_TS E2 W2 _ _ live peak (cnt + 1) fail (SOff 35 0) (SOff 36 0) (SOff 33 0) (SOff 34 0) HM5).
  all: first
    [ solve [lazymatch goal with |- fs_pstat_find _ _ = Some _ => vm_compute; reflexivity end]
    | solve [rewrite fsw_SOff0; exact (EX2 3%nat (Z_to_bv 64 live) eq_refl)]
    | solve [rewrite fsw_SOff0; exact (EX2 4%nat (Z_to_bv 64 peak) eq_refl)]
    | solve [rewrite fsw_SOff0; exact (EX2 1%nat (Z_to_bv 64 (cnt + 1)) eq_refl)]
    | solve [rewrite fsw_SOff0; exact (EX2 2%nat (Z_to_bv 64 fail) eq_refl)]
    | solve [lia] ]. }
(* ... kept across the call (they are image bytes, far below the call's stack window) *)
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> a < SHADOW_OFF \/ kHighMemBeg <= a -> a + 1 <= spZ regs - 16416 ->
  mbyte tfibsegs (mrestrict (w_H W2) mem3) a = mbyte tfibsegs (mrestrict (w_H W2) (ms_mem ms0)) a).
{ intros a Ha Happ' Hlo.
  apply (fm_keep_app ly2 S2 U (U ++ [(b, 16)]) W2 (ms_mem ms0) mem3 _ md3 (spZ (ms_regs ms0)) a HARU3 HARU4 HAK Ha Happ').
  unfold PO_WIN. rewrite T2. lia. }
assert (G3 : fs_glob tfibsegs W2 mem3 live peak (cnt + 1) fail).
{ apply (fm_glob_keep W2 W2 (ms_mem ms0) mem3 live peak (cnt + 1) fail G0). intros a Ha.
  pose proof (fm_pstat_bounds a Ha) as Hb.
  apply KEEP; unfold G_FAIL, G_LIVE, G_PEAK, G_COUNT, SHADOW_OFF in *; rewrite FM in Hceil; lia. }
assert (Hval3 : val_mem tfibsegs (mrestrict (w_H W2) mem3) b 8 n).
{ intros k Hk. rewrite KEEP; [exact (Hval0 k Hk) | | |].
  all: rewrite ?Hrq in Happ; unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *;
       rewrite ?Hrq in Hbceil; unfold ASAN_CEIL in *; rewrite FM in Hceil; lia. }
assert (Hck3 : Forall (YP09.chunk_ok tfibsegs E3 (mrestrict (w_H W2) (ms_mem ms0)) (spZ regs - 32)) fm_cs).
{ unfold fm_cs. unfold fm_cs in Hck. clear Hck.
  pose proof HCK5 as H0.
  pose proof (Forall_inv H0) as K40. apply Forall_inv_tail in H0.
  pose proof (Forall_inv H0) as K39. apply Forall_inv_tail in H0.
  pose proof (Forall_inv H0) as K38. apply Forall_inv_tail in H0.
  pose proof (Forall_inv H0) as K37.
  repeat constructor.
  - apply (fm_chunk_move E2 E3 _ (spZ regs - 32) (spZ regs - 32) 0 0 8 (SOff 40 0) (SOff 40 0)); [lia | | exact K40].
    cbn [sv_denot]; f_equal; try (f_equal; exact (A23 8%nat)).
  - apply (fm_chunk_move E2 E3 _ (spZ regs - 32) (spZ regs - 32) 8 8 8 (SOff 39 0) (SOff 39 0)); [lia | | exact K39].
    cbn [sv_denot]; f_equal; try (f_equal; exact (A23 7%nat)).
  - apply (fm_chunk_move E2 E3 _ (spZ regs - 32) (spZ regs - 32) 16 16 8 (SOff 38 0) (SOff 38 0)); [lia | | exact K38].
    cbn [sv_denot]; f_equal; try (f_equal; exact (A23 6%nat)).
  - apply (fm_chunk_move E2 E3 _ (spZ regs - 32) (spZ regs - 32) 24 24 8 (SOff 37 0) (SOff 37 0)); [lia | | exact K37].
    cbn [sv_denot]; f_equal; try (f_equal; exact (A23 5%nat)). }
assert (Hpdj3 : pairwise_disjoint E3 (fsT_ret_regions 32 fm_cs fs_pstat_regions)).
{ apply pairwise_disjoint_of_extents.
  unfold fsT_ret_regions, fs_pstat_regions, fs_got_region, fs_bcell_region, fstk_ret, fs_pstat_region, extent_of_region.
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E3_2.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address,
    G_COUNT, G_FAIL, G_LIVE, G_PEAK in *.
  rewrite FM in Hceil.
  cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia | lia]. }
pose proof (fsw_resume_after_rtU_args B STK_fuzz_malloc (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md [] ly2 S2
  (U ++ [(b, 16)]) W2 mem3 md3 (0 + 1) (ms_regs ms0) regs3 (ms_mem ms0) 32 (fm_xs regs cnt fail live peak) fm_cs
  fs_pstat_regions [] A_fuzz_malloc_ra_po FS_GOT_SHADOW FS_SHADOW_CELL HJ3 HARU4 HP3
  ltac:(rewrite T2; lia) ltac:(lia) ltac:(rewrite FM; lia) eq_refl ltac:(vm_compute; reflexivity)
  ltac:(unfold fm_cs; repeat constructor; cbn; lia) Hck3
  ltac:(intros a Ha; apply HFK; rewrite T2; lia)
  (fm_pstat_ok W2 regs3 mem3 live peak (cnt + 1) fail [getr regs 1; getr regs 8; getr regs 9; getr regs 18] G3)
  Hpdj3 ltac:(first [exact I | constructor])) as HS6.
apply (fm_tail ly S U W regs mem md n live peak cnt fail ly2 S2 W2 regs3 mem3 md3 b HS6 HJ3 HARU4).
all: first
  [ solve [exact Hbl] | solve [exact FH] | solve [exact Hval3] | solve [exact IS] | solve [exact Hra]
  | solve [exact Hb16] | solve [exact Hn1] | solve [exact Hlv] | solve [exact Hb4096]
  | solve [lazymatch goal with |- spZ _ = _ => unfold spZ; rewrite Q2; unfold spZ in T2; lia end]
  | solve [lazymatch goal with |- getr _ 8 = _ => rewrite Q8; exact T8 end]
  | solve [lazymatch goal with |- getr _ 9 = _ => rewrite Q9; exact T9 end]
  | solve [lazymatch goal with |- forall r, acallee_saved r -> _ =>
      intros r Hcs H2 H8 H9 H18; rewrite (HP3 r Hcs);
      assert (Hr : In r [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]) by (cbn; unfold acallee_saved in Hcs; lia);
      repeat (destruct Hr as [<- | Hr]); [..| destruct Hr];
      lazymatch goal with |- getr _ (Z_to_bv 5 ?z) = _ =>
        let k := eval vm_compute in (Z.to_nat z) in
        transitivity (getr regs2 (Z_to_bv 5 z));
        [ exact (fsw_reg_atom (w_H W2) regs2 (fs_extraT ++ xs) _ ms0 (Z_to_bv 5 z) (Z_to_bv 5 z) k HS5
                   ltac:(vm_compute; reflexivity) eq_refl)
        | transitivity (getr (ms_regs ms1) (Z_to_bv 5 z));
          [ exact (HP z ltac:(unfold acallee_saved; lia))
          | exact (fsw_reg_atom (w_H W) regs (fs_extraTS cnt fail live peak) _ ms1 (Z_to_bv 5 z) (Z_to_bv 5 z) k HS3
                     ltac:(vm_compute; reflexivity) eq_refl) ] ] end end]
  | solve [lazymatch goal with |- _ + (_ + HEAD) <= _ => rewrite ?Hrq in Hbceil; unfold HEAD in *; lia end]
  | solve [lia] ].
Qed.

(* fuzz_malloc_spec of lib/A/FSH_Fn_alloc.v: the two arms, by failing() *)
Theorem fuzz_malloc_holds : @fuzz_malloc_spec fx rc SK tfibsegs B.
Proof.
unfold fuzz_malloc_spec.
intros ly S U W regs mem md ch n live peak cnt fail HPRE FH H10 Hn1 Hn2 HGL Hlv Hcn Hev Hbb.
destruct (Z.eq_dec cnt fail) as [Hcf | Hcf].
- eapply SRr_mono; [exact (fm_null_arm B IMG SHS ly S U W regs mem md ch live peak cnt fail HPRE FH HGL Hcn Hcf) |].
  intros W' c' _ HQ. left. split; [exact Hcf | exact HQ].
- eapply SRr_mono;
    [exact (fm_malloc_arm ly S U W regs mem md ch n live peak cnt fail HPRE FH H10 Hn1 Hn2 HGL (Hlv Hcf) Hcn Hev
              (Hbb Hcf) Hcf) |].
  intros W' c' _ HQ. right. split; [exact Hcf | exact HQ].
Qed.

End m.
