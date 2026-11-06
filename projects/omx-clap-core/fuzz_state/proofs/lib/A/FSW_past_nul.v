(* past_nul 0x82728 (fuzz_state.c) over fs.asan: the ASan walk proving FSH_Fn_cno.v's past_nul_spec at fs.asan's image
   (tfibsegs), build A's sink head AE2k.tfib_sink_head passed explicitly (FSH_Harness.v guard). The spec is CTX-free (the
   owner's 05:05Z CTX drop): no caller context and no trace premise, here or in any callee step.
   The walk (71 instructions, real 64-byte frame, plain T entry fss0T / fsw_entryT, no re-align):
   - the entry run to the HARNESS allocator `jal __wrap_malloc` 0x82768 with a0 = n + 18; the call is ALLOC's
     FSW_malloc_free.fsw_aj_malloc04U (the U form of YCbq.aj_malloc_at04: the non-NULL block (res, n + 18) appended, U
     unchanged, no fuzz HEAD, no poison, the alloc.c statics untouched); its event-room premise st_nev S < EV_MAX is the
     spec's budget st_nev S + EV_past_nul <= EV_MAX (EV_past_nul = 1), from which the kit takes the SECOND disjunct of
     amalloc_realizesU's `In (call_trace ..) (as_universe B) \/ st_nev S < EV_MAX`; the resume is
     FSW_rres.fsw_resume_after_rtU_args_chunks;
   - `beqz a0` 0x8276c (-> 0x82814 `jal __asan_handle_no_return`; `jal abort`) is untaken: res >= 4096 (exfalso);
   - `beqz s2` 0x82774 splits n = 0 (no copy) from n > 0, each case closing the other arm by exfalso: `jal __asan_memcpy`
     0x82784 copies the n source bytes (the spec's source-block premise keeps them across the malloc and makes the copy's
     ranges disjoint), FSW_K.fsw_intrin_atU;
   - `jal __asan_memset` 0x827a0 zeroes [res + n, res + n + 17) (pn_tail);
   - the three inline-checked byte stores (c at res + n + 1, 'A' at res + n + 2, NUL at res + n + 17): FSW_K's token run
     fsw_aj_run_tokU. The three `__asan_report_store1` arms (report-sites-A.tsv rows 0x82828 deciding 0x827b0:bne,
     0x82834 deciding 0x827c8:bne, 0x82840 deciding 0x827e0:bne, the function's last instruction) are UNTAKEN in that run:
     pn_SH's two shadow entries (s2 + [0, 3), s3 + [0, 1)) are range_addressable on the machine's memory (the new block's
     shadow holds no user-poisoned byte: pn_ush_new), so each check reads a zero shadow byte and the run reaches the `ret`
     with no open shadow obligation (FSW_past_nul_tbl.pn_run_memset);
   - the return: FSW_ret.fsw_retU to apost_baseU with U' = U, k = EV_past_nul = 1, the block appended, pn_copy db c at res,
     the alloc.c statics unchanged (journal image clause, fs_img_facts' FS_PSTAT_FP conjunct), the heads U still in
     their (old) blocks.
   Control flow template: fs's released plain lib/Prog/past_nul.v (read for the instruction sequence only).
   Callee contracts taken as Section hypotheses: the FsRt fields fr_malloc, fr_memcpy, fr_memset (FSH_Rt.v), the image
   facts fs_img_facts, api_env, model_laws, and the two shadow-base cells of B. The image hull is A/AD1y.v in_img_hull.
   Every multi-premise apply discharges its premises per goal, each alternative guarded by the goal's shape (FSW_K kit
   rule R1). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_ret FSW_rres FSW_malloc_free FSH_Fn_cno
FSW_past_nul_tbl.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require AE2k AD1y.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Ltac pn_csv := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?q] => let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia.

Ltac pn_sr HS q := rewrite (st_ok_restrict_reg tfibsegs _ _ _ _ q HS);
  lazymatch goal with |- context [sr_get ?l q] => let v := eval vm_compute in (sr_get l q) in change (sr_get l q) with v end.

(* the machine value of register q after a run, from the symbolic state and the env's atom equations in context *)
Ltac pn_val HS q E :=
  unfold w64; pn_sr HS q; rewrite denot_lit_U; f_equal;
  rewrite ?U_SAlu; cbn [zalu_raw];
  repeat match goal with
   | H : ew E ?k = Z_to_bv 64 ?v |- context [YP0e.U E (SOff ?k ?c)] =>
       rewrite (U_atom_off E k v c H) by (unfold SHADOW_OFF in *; lia)
   end;
  rewrite ?U_lit by lia;
  try (rewrite zcanon_id; [|unfold M64, SHADOW_OFF in *; lia]); unfold SHADOW_OFF in *; lia.

Ltac pn_rcsv HS VQ :=
  let q := fresh "q" in let Hq := fresh "Hq" in
  intros q Hq;
  assert (Hq' : q = 3 \/ q = 4 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia;
  destruct Hq' as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]];
  lazymatch goal with |- getr _ ?r = _ => pn_sr HS r end; rewrite fsw_SOff0;
  lazymatch goal with |- ew _ ?k = _ => rewrite (VQ k ltac:(lia)); reflexivity end.

(* the write-window obligations (awr_ok) of the walk's runs, per goal (kit rule R1): the side goals of one cons step,
   each closed by the tactic of its kind; the tail awr_ok goal is kept *)
Ltac pn_awr_side Esp :=
  first [ lazymatch goal with |- _ = Some _ => solve [reflexivity] end
        | lazymatch goal with |- bv_unsigned _ = _ => solve [rewrite Esp; lia] end
        | lazymatch goal with |- (_ <= _)%Z => solve [cbn; lia] end ].
Ltac pn_awr_keep := lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ => idtac end.
(* the two read-only shadow-base cells of a T state *)
Ltac pn_awr_cells Esp :=
  apply awr_ok_cons_ro; first [ solve [pn_awr_side Esp] | pn_awr_keep ];
  apply awr_ok_cons_ro; first [ solve [pn_awr_side Esp] | pn_awr_keep ].
(* a T state resumed after a call: the frame region (atom 2 = sp0 - 64, window [0, 64)), then the two cells; the
   state's own rs regions are left as the tail goal *)
Ltac pn_awr_ret Esp :=
  unfold fss_retT, fsT_ret_regions; cbn [add_cond ss_mem app];
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -64); first [ solve [pn_awr_side Esp] | pn_awr_keep ];
  pn_awr_cells Esp.

(* one saved register's chunk of the after-call frame (pn_frame_cs): the chunk_ok_val premises, per goal *)
Ltac pn_cok X j V :=
  first [ lazymatch goal with |- sv_denot _ _ = _ => solve [exact (X j _ ltac:(lia) eq_refl)] end
        | lazymatch goal with |- (0 <= _ < _)%Z => solve [apply u64_range] end
        | lazymatch goal with |- (Z.of_N _ <= _)%Z => solve [cbn; lia] end
        | lazymatch goal with |- val_mem _ _ ?a _ _ =>
            lazymatch type of V with val_mem _ _ ?b _ _ => solve [replace a with b by lia; exact V] end end ].

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Abbreviation SKA := AE2k.tfib_sink_head.
Variable B : asyms.
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis HGOT : as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address.
Hypothesis HCELL : as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address.
Hypothesis FS_ENV : api_env tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FR_MALLOC : pc_wrap_malloc (as_code B) = PC_malloc /\ FSupoisonU.amalloc_realizesU tfibsegs B.
Hypothesis FR_MEMCPY : FSupoisonU.aintrin_realizesU tfibsegs B OCpy PC_memcpy.
Hypothesis FR_MEMSET : FSupoisonU.aintrin_realizesU tfibsegs B OSet PC_memset.

Definition pn_xs (regs : bvmap 5 word) : list word :=
  [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21].
Definition pn_frame (H : word -> bool) (m : word -> option byte) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
  val_mem tfibsegs (mrestrict H m) (sp0 - 8) 8 (bv_unsigned (getr regs 1)) /\
  val_mem tfibsegs (mrestrict H m) (sp0 - 16) 8 (bv_unsigned (getr regs 8)) /\
  val_mem tfibsegs (mrestrict H m) (sp0 - 24) 8 (bv_unsigned (getr regs 9)) /\
  val_mem tfibsegs (mrestrict H m) (sp0 - 32) 8 (bv_unsigned (getr regs 18)) /\
  val_mem tfibsegs (mrestrict H m) (sp0 - 40) 8 (bv_unsigned (getr regs 19)) /\
  val_mem tfibsegs (mrestrict H m) (sp0 - 48) 8 (bv_unsigned (getr regs 20)) /\
  val_mem tfibsegs (mrestrict H m) (sp0 - 56) 8 (bv_unsigned (getr regs 21)).
Lemma pn_frame_kept : forall H H' m m' sp0 regs, pn_frame H m sp0 regs ->
  (forall a, sp0 - 64 <= a < sp0 -> aview tfibsegs H' m' a = aview tfibsegs H m a) -> pn_frame H' m' sp0 regs.
Proof.
intros H H' m m' sp0 regs (V1 & V2 & V3 & V4 & V5 & V6 & V7) K.
unfold pn_frame. repeat split;
  (eapply val_mem_kept;
   first [ lazymatch goal with |- forall _, _ => solve [intros k Hk; apply K; cbn in Hk; lia] end
         | lazymatch goal with |- val_mem _ _ _ _ _ => solve [eassumption] end ]).
Qed.
Lemma pn_frame_cs : forall H m sp0 regs regs2, pn_frame H m sp0 regs ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs2 (fs_extraT ++ pn_xs regs)) (mrestrict H m) (sp0 - 64)) pn_cs.
Proof.
intros H m sp0 regs regs2 (V1 & V2 & V3 & V4 & V5 & V6 & V7).
assert (X : forall j r, (j < 8)%nat -> nth j (fs_extraT ++ pn_xs regs) (Z_to_bv 64 0) = r ->
  sv_denot (Ereg regs2 (fs_extraT ++ pn_xs regs)) (SOff (32 + j) 0) = Z_to_bv 64 (bv_unsigned r)).
{ intros j r Hj Hr. rewrite fsw_SOff0, ew_Ereg_extra, Hr. symmetry. apply Z_to_bv_bv_unsigned. }
unfold pn_cs. repeat constructor.
- apply (chunk_ok_val tfibsegs _ _ _ 56 8%N (SOff 33 0) (bv_unsigned (getr regs 1))); pn_cok X 1%nat V1.
- apply (chunk_ok_val tfibsegs _ _ _ 48 8%N (SOff 34 0) (bv_unsigned (getr regs 8))); pn_cok X 2%nat V2.
- apply (chunk_ok_val tfibsegs _ _ _ 40 8%N (SOff 35 0) (bv_unsigned (getr regs 9))); pn_cok X 3%nat V3.
- apply (chunk_ok_val tfibsegs _ _ _ 32 8%N (SOff 36 0) (bv_unsigned (getr regs 18))); pn_cok X 4%nat V4.
- apply (chunk_ok_val tfibsegs _ _ _ 24 8%N (SOff 37 0) (bv_unsigned (getr regs 19))); pn_cok X 5%nat V5.
- apply (chunk_ok_val tfibsegs _ _ _ 16 8%N (SOff 38 0) (bv_unsigned (getr regs 20))); pn_cok X 6%nat V6.
- apply (chunk_ok_val tfibsegs _ _ _ 8 8%N (SOff 39 0) (bv_unsigned (getr regs 21))); pn_cok X 7%nat V7.
Qed.

Definition pn_entry_region : YP09.region :=
  YP09.mkRegion (Some 2%nat) (-64) 0 (-64) 0
    [YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
     YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
     YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Lemma pn_frame_of_entry : forall regs H mm sp0,
  region_ok tfibsegs (Ereg regs fs_extraT) (mrestrict H mm) pn_entry_region ->
  bv_unsigned (ew (Ereg regs fs_extraT) 2) = sp0 -> pn_frame H mm sp0 regs.
Proof.
intros regs H mm sp0 HR Hsp.
assert (X : forall (r : nat) (q : bv 5), Z.of_nat r = bv_unsigned q ->
  sv_denot (Ereg regs fs_extraT) (SOff r 0) = Z_to_bv 64 (bv_unsigned (getr regs q))).
{ intros r q Hq. rewrite fsw_SOff0, (ew_Ereg_nat regs fs_extraT r q Hq). symmetry. apply Z_to_bv_bv_unsigned. }
unfold pn_frame, pn_entry_region in *.
repeat split.
- exact (fsw_field _ _ 2 sp0 _ _ _ _ _ (-8) 8%N (SOff 1 0) _ HR Hsp ltac:(cbn; tauto) (X 1%nat 1%bv eq_refl) (u64_range _) ltac:(cbn; lia)).
- exact (fsw_field _ _ 2 sp0 _ _ _ _ _ (-16) 8%N (SOff 8 0) _ HR Hsp ltac:(cbn; tauto) (X 8%nat 8%bv eq_refl) (u64_range _) ltac:(cbn; lia)).
- exact (fsw_field _ _ 2 sp0 _ _ _ _ _ (-24) 8%N (SOff 9 0) _ HR Hsp ltac:(cbn; tauto) (X 9%nat 9%bv eq_refl) (u64_range _) ltac:(cbn; lia)).
- exact (fsw_field _ _ 2 sp0 _ _ _ _ _ (-32) 8%N (SOff 18 0) _ HR Hsp ltac:(cbn; tauto) (X 18%nat 18%bv eq_refl) (u64_range _) ltac:(cbn; lia)).
- exact (fsw_field _ _ 2 sp0 _ _ _ _ _ (-40) 8%N (SOff 19 0) _ HR Hsp ltac:(cbn; tauto) (X 19%nat 19%bv eq_refl) (u64_range _) ltac:(cbn; lia)).
- exact (fsw_field _ _ 2 sp0 _ _ _ _ _ (-48) 8%N (SOff 20 0) _ HR Hsp ltac:(cbn; tauto) (X 20%nat 20%bv eq_refl) (u64_range _) ltac:(cbn; lia)).
- exact (fsw_field _ _ 2 sp0 _ _ _ _ _ (-56) 8%N (SOff 21 0) _ HR Hsp ltac:(cbn; tauto) (X 21%nat 21%bv eq_refl) (u64_range _) ltac:(cbn; lia)).
Qed.

Lemma pn_unp_app : forall ly S U (W : world tfibsegs) mem md a, ARU tfibsegs B ly S U W mem md -> 0 <= a < 2 ^ 64 ->
  (a < SHADOW_OFF \/ kHighMemBeg <= a) -> unpoison U mem (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
intros ly S U W mem md a H Ha [Hl|Hh].
- exact (ARU_mem_low tfibsegs B ly S U W mem md (Z_to_bv 64 a) H ltac:(rewrite wz by lia; exact Hl)).
- apply (fsw_unpoison_high B ly S U W mem md a H). lia.
Qed.
Lemma pn_view_app : forall ly S U (W : world tfibsegs) mem md a, ARU tfibsegs B ly S U W mem md -> 0 <= a < 2 ^ 64 ->
  (a < SHADOW_OFF \/ kHighMemBeg <= a) -> aview tfibsegs (w_H W) (unpoison U mem) a = aview tfibsegs (w_H W) mem a.
Proof. intros. apply aview_at. eapply pn_unp_app; eassumption. Qed.
Lemma pn_ush_new : forall ly S U (W : world tfibsegs) mem md p q x, ARU tfibsegs B ly S U W mem md ->
  (forall b m, In (b, m) (ablocks B ly S) -> zdisjoint (b, req_size m) (p, q)) -> p <= x < p + q -> 0 <= x < 2 ^ 64 ->
  in_ush U (bv_unsigned (Z_to_bv 64 (shadow_addr x))) = false.
Proof.
intros ly S U W mem md p q x H Hd Hx Hx64. apply (ARU_shadow_out_block tfibsegs B ly S U W mem md x H Hx64).
intros b m Hb Hin. specialize (Hd b m Hb). unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
Lemma pn_ra_raw : forall ly S U (W : world tfibsegs) m md p k a len, ARU tfibsegs B ly S U W m md ->
  In (p, k) (ablocks B ly S) -> p <= a -> a + len <= p + req_size k ->
  (forall x, a <= x < a + len -> in_ush U (bv_unsigned (Z_to_bv 64 (shadow_addr x))) = false) ->
  range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF a len.
Proof.
intros ly S U W m md p k a len H Hin H1 H2 Hu.
apply (range_addressable_agree (aview tfibsegs (w_H W) (unpoison U m)));
  first
  [ lazymatch goal with |- range_addressable _ _ _ _ =>
      solve [exact (range_addressable_of_block tfibsegs B (AR_laws_ok tfibsegs B) ly S W (unpoison U m) md p k a len
               (ARU_AR _ _ _ _ _ _ _ _ H) Hin H1 H2)] end
  | lazymatch goal with |- forall _, _ =>
      solve [intros x Hx; change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x);
             symmetry; apply (aview_unpoison_out tfibsegs); exact (Hu x Hx)] end ].
Qed.
Lemma pn_hull_raw : forall ly S U (W : world tfibsegs) m md a len, ARU tfibsegs B ly S U W m md ->
  shadow_hull_vis (aview tfibsegs (w_H W) (unpoison U m)) a len -> shadow_hull_vis (aview tfibsegs (w_H W) m) a len.
Proof.
intros ly S U W m md a len (HAR & OK & PO) Hh s Hs.
rewrite aview_mod. destruct (in_ush U (s mod 2 ^ 64)) eqn:Ei.
- rewrite (PO _ Ei). discriminate.
- rewrite <- aview_mod. rewrite <- (aview_unpoison_out tfibsegs (w_H W) U m s); [exact (Hh s Hs)|].
  rewrite Z_to_bv_unsigned. exact Ei.
Qed.
Lemma pn_garr8 : forall H m base l, Forall (fun z => 0 <= z < 256) l ->
  (forall j, (j < length l)%nat -> aview tfibsegs H m (base + Z.of_nat j) = Some (nth j l 0)) ->
  garr8 tfibsegs (mrestrict H m) base l.
Proof.
intros H m base l Hb Hv j Hj.
assert (Bj : 0 <= nth j l 0 < 256) by (exact (proj1 (Forall_nth _ l) Hb j 0 Hj)).
split; [|exact Bj]. intros k Hk. assert (k = 0%nat) as -> by lia.
destruct (aview_byte tfibsegs H m _ _ (Hv j Hj)) as (b & Hm & Ev & _).
rewrite Z.add_0_r. rewrite Hm. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
unfold YO0f.le_byte. cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.shiftr_0_r. change (2 ^ (8 * 1)) with 256.
rewrite !Z.mod_small by lia. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. lia.
Qed.
Lemma pn_aview_of_garr8 : forall H m base l j, garr8 tfibsegs (mrestrict H m) base l -> (j < length l)%nat ->
  aview tfibsegs H m (base + Z.of_nat j) = Some (nth j l 0).
Proof.
intros H m base l j Hg Hj. destruct (Hg j Hj) as [Hv Bj]. specialize (Hv 0%nat ltac:(lia)).
rewrite Z.add_0_r in Hv. unfold aview. rewrite Hv. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold YO0f.le_byte. cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.shiftr_0_r. change (2 ^ (8 * 1)) with 256.
rewrite !Z.mod_small by lia. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia.
Qed.

Definition pn_Q (U : list (Z * Z)) (ly : alayout) (S : astate) (n c res live peak cnt fail : Z) (db : list Z)
  : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' W' regs' mem' _ =>
    getr regs' 10 = w64 res /\ res <> 0 /\ res mod 16 = 0 /\
    ablocks B ly' S' = ablocks B ly S ++ [(res, n + 18)] /\
    fs_heads B ly' S' U /\ zbytes_at tfibsegs W' mem' res (pn_copy db c) /\
    fs_glob tfibsegs W' mem' live peak cnt fail.

Lemma pn_chunk1 : forall E H m base off e v,
  YP09.chunk_ok tfibsegs E (mrestrict H m) base (YP09.mkChunk off (CVal 1 e)) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> aview tfibsegs H m (base + off) = Some (v mod 256).
Proof.
intros E H m base off e v Hc He Hv.
destruct (Hc 0 ltac:(cbn; lia)) as (b & Hb & Hm). cbn [YP09.c_off YP09.c_val cbyte] in Hb, Hm.
injection Hb as <-. rewrite Z.add_0_r in Hm. unfold aview. rewrite Hm. cbn [option_map]. f_equal.
unfold byte_of_word. rewrite He, Z.shiftr_0_r, Z_to_bv_unsigned, wz by exact Hv.
unfold bv_wrap. reflexivity.
Qed.
Lemma pn_glob_kept : forall (W W' : world tfibsegs) mem mem' live peak cnt fail,
  fs_glob tfibsegs W mem live peak cnt fail ->
  (forall a, inFP FS_PSTAT_FP a -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) ->
  fs_glob tfibsegs W' mem' live peak cnt fail.
Proof.
intros W W' mem mem' live peak cnt fail (G1 & G2 & G3 & G4 & GR) K.
assert (KV : forall g v, In (g, g + 8) FS_PSTAT_FP -> val_mem tfibsegs (mrestrict (w_H W) mem) g 8 v ->
  val_mem tfibsegs (mrestrict (w_H W') mem') g 8 v).
{ intros g v Hg Hv. apply (val_mem_kept tfibsegs (w_H W) (w_H W') mem mem' g 8 v);
    first [ lazymatch goal with |- val_mem _ _ _ _ _ => solve [exact Hv] end
          | lazymatch goal with |- forall _, _ =>
              solve [intros k Hk; apply K; apply (inFP_FS_PSTAT_FP g Hg); cbn in Hk; lia] end ]. }
unfold fs_glob, fs_glob_at. split; [|split; [|split; [|split]]].
- apply KV; first [ solve [exact G1] | lazymatch goal with |- In _ _ => solve [unfold FS_PSTAT_FP, G_LIVE; cbn; tauto] end ].
- apply KV; first [ solve [exact G2] | lazymatch goal with |- In _ _ => solve [unfold FS_PSTAT_FP, G_PEAK; cbn; tauto] end ].
- apply KV; first [ solve [exact G3] | lazymatch goal with |- In _ _ => solve [unfold FS_PSTAT_FP, G_COUNT; cbn; tauto] end ].
- apply KV; first [ solve [exact G4] | lazymatch goal with |- In _ _ => solve [unfold FS_PSTAT_FP, G_FAIL; cbn; tauto] end ].
- exact GR.
Qed.

(* the callee-saved registers at the `ret`: sp back up by the frame, s0 .. s5 reloaded from the frame (extra atoms
   34 .. 39), the rest the entry atoms *)
Definition pn_expect (r : bv 5) : sv :=
  match bv_unsigned r with 2 => SOff 2 64 | 8 => SOff 34 0 | 9 => SOff 35 0 | 18 => SOff 36 0
  | 19 => SOff 37 0 | 20 => SOff 38 0 | 21 => SOff 39 0 | z => SOff (Z.to_nat z) 0 end.

Lemma pn_copy_len : forall db c, length (pn_copy db c) = (length db + 18)%nat.
Proof. intros db c. unfold pn_copy. rewrite !length_app, repeat_length. reflexivity. Qed.
Lemma pn_copy_head : forall db c j, (j < length db)%nat -> nth j (pn_copy db c) 0 = nth j db 0.
Proof. intros db c j Hj. unfold pn_copy. apply app_nth1. exact Hj. Qed.
Lemma pn_copy_tail : forall db c k, (k < 18)%nat ->
  nth (length db + k) (pn_copy db c) 0 = nth k ([0; c mod 256; 65] ++ repeat 0 15) 0.
Proof. intros db c k Hk. unfold pn_copy. rewrite app_nth2 by lia. f_equal. lia. Qed.
Lemma pn_copy_bytes : forall db c, Forall (fun z => 0 <= z < 256) db -> Forall (fun z => 0 <= z < 256) (pn_copy db c).
Proof.
intros db c Hdb. unfold pn_copy. apply Forall_app. split; [exact Hdb|].
apply Forall_app. split.
- repeat constructor; try lia; apply Z.mod_pos_bound; lia.
- apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia.
Qed.

Lemma pn_frame_of_cs : forall E H m sp0 regs,
  (forall j, (j < 8)%nat -> ew E (32 + j) = nth j (fs_extraT ++ pn_xs regs) (Z_to_bv 64 0)) ->
  bv_unsigned (ew E 2) = sp0 - 64 ->
  region_ok tfibsegs E (mrestrict H m) (fstk_ret 64 pn_cs) -> pn_frame H m sp0 regs.
Proof.
intros E H m sp0 regs EX Hsp HR.
assert (X : forall j r, (j < 8)%nat -> nth j (fs_extraT ++ pn_xs regs) (Z_to_bv 64 0) = r ->
  sv_denot E (SOff (32 + j) 0) = Z_to_bv 64 (bv_unsigned r)).
{ intros j r Hj Hr. rewrite fsw_SOff0, EX, Hr by exact Hj. symmetry. apply Z_to_bv_bv_unsigned. }
unfold pn_frame, fstk_ret, pn_cs in *.
repeat split.
- pose proof (fsw_field _ _ 2 (sp0 - 64) _ _ _ _ _ 56 8%N (SOff 33 0) _ HR Hsp ltac:(cbn; tauto) (X 1%nat _ ltac:(lia) eq_refl) (u64_range _) ltac:(cbn; lia)) as V.
  replace (sp0 - 64 + 56) with (sp0 - 8) in V by lia. exact V.
- pose proof (fsw_field _ _ 2 (sp0 - 64) _ _ _ _ _ 48 8%N (SOff 34 0) _ HR Hsp ltac:(cbn; tauto) (X 2%nat _ ltac:(lia) eq_refl) (u64_range _) ltac:(cbn; lia)) as V.
  replace (sp0 - 64 + 48) with (sp0 - 16) in V by lia. exact V.
- pose proof (fsw_field _ _ 2 (sp0 - 64) _ _ _ _ _ 40 8%N (SOff 35 0) _ HR Hsp ltac:(cbn; tauto) (X 3%nat _ ltac:(lia) eq_refl) (u64_range _) ltac:(cbn; lia)) as V.
  replace (sp0 - 64 + 40) with (sp0 - 24) in V by lia. exact V.
- pose proof (fsw_field _ _ 2 (sp0 - 64) _ _ _ _ _ 32 8%N (SOff 36 0) _ HR Hsp ltac:(cbn; tauto) (X 4%nat _ ltac:(lia) eq_refl) (u64_range _) ltac:(cbn; lia)) as V.
  replace (sp0 - 64 + 32) with (sp0 - 32) in V by lia. exact V.
- pose proof (fsw_field _ _ 2 (sp0 - 64) _ _ _ _ _ 24 8%N (SOff 37 0) _ HR Hsp ltac:(cbn; tauto) (X 5%nat _ ltac:(lia) eq_refl) (u64_range _) ltac:(cbn; lia)) as V.
  replace (sp0 - 64 + 24) with (sp0 - 40) in V by lia. exact V.
- pose proof (fsw_field _ _ 2 (sp0 - 64) _ _ _ _ _ 16 8%N (SOff 38 0) _ HR Hsp ltac:(cbn; tauto) (X 6%nat _ ltac:(lia) eq_refl) (u64_range _) ltac:(cbn; lia)) as V.
  replace (sp0 - 64 + 16) with (sp0 - 48) in V by lia. exact V.
- pose proof (fsw_field _ _ 2 (sp0 - 64) _ _ _ _ _ 8 8%N (SOff 39 0) _ HR Hsp ltac:(cbn; tauto) (X 7%nat _ ltac:(lia) eq_refl) (u64_range _) ltac:(cbn; lia)) as V.
  replace (sp0 - 64 + 8) with (sp0 - 56) in V by lia. exact V.
Qed.
Lemma pn_ush_src : forall (W : world tfibsegs) mem U d n, range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF d n ->
  upoisoned tfibsegs W mem U -> forall x, d <= x < d + n -> 0 <= x < 2 ^ 63 ->
  in_ush U (bv_unsigned (Z_to_bv 64 (shadow_addr x))) = false.
Proof.
intros W mem U d n Hra Hpo x Hx Hx0.
assert (Hs : 0 <= shadow_addr x < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF. split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
  pose proof (Z.div_le_mono x (2 ^ 63) 8 ltac:(lia) ltac:(lia)). change (2 ^ 63 / 8) with (2 ^ 60) in H. lia. }
rewrite wz by exact Hs. destruct (in_ush U (shadow_addr x)) eqn:Ei; [|reflexivity].
exfalso. pose proof (Hpo _ Ei) as Hp. destruct (Hra x Hx) as (s & Hsv & Hok).
change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x) in Hsv. rewrite Hp in Hsv. injection Hsv as <-.
unfold saddr_ok in Hok. lia.
Qed.

Lemma pn_tail : forall ly S U (W : world tfibsegs) regs mem md n c (db : list Z) live peak cnt fail
    res ly2 S2 (W2 : world tfibsegs) regsT memT mdc,
  ret_ok (getr regs 1) -> fs_heads B ly S U -> fs_glob tfibsegs W mem live peak cnt fail ->
  0 <= c < 2 ^ 64 -> 0 <= n <= 2 ^ 22 -> Z.of_nat (length db) = n -> Forall (fun z => 0 <= z < 256) db ->
  ARU tfibsegs B ly S U W mem md ->
  ajournal (SK := SKA) tfibsegs B STK_past_nul (spZ regs) [] ly S W (unpoison U mem) md [] ly2 S2 W2
    (unpoison U memT) mdc 1 ->
  ARU tfibsegs B ly2 S2 U W2 memT mdc ->
  ablocks B ly2 S2 = ablocks B ly S ++ [(res, n + 18)] ->
  getr regsT 1 = Z_to_bv 64 RA_PN_MEMSET -> spZ regsT = spZ regs - 64 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 10 = w64 (res + n) -> getr regsT 11 = w64 0 -> getr regsT 12 = w64 17 ->
  getr regsT 8 = w64 res -> getr regsT 9 = w64 c -> getr regsT 18 = w64 (res + n) ->
  getr regsT 19 = w64 (res + n + 17) -> getr regsT 21 = w64 SHADOW_OFF ->
  (forall q, (q = 3 \/ q = 4 \/ 22 <= q <= 27) -> getr regsT (Z_to_bv 5 q) = getr regs (Z_to_bv 5 q)) ->
  pn_frame (w_H W2) memT (spZ regs) regs ->
  (forall i, 0 <= i < n -> aview tfibsegs (w_H W2) memT (res + i) = Some (nth (Z.to_nat i) db 0)) ->
  SRr tfibsegs W2 (mkCfg (mkst regsT (Z_to_bv 64 PC_memset) memT (seg_rom tfibsegs)) mdc)
    (fun W' c' => exists res0, apost_baseU (SK := SKA) tfibsegs B STK_past_nul [] regs ly S W mem md EV_past_nul U U
       (pn_Q U ly S n c res0 live peak cnt fail db) W' c').
Proof.
intros ly S U W regs mem md n c db live peak cnt fail res ly2 S2 W2 regsT memT mdc
  Hra FH HG Hc Hn Hlen Hdb HARU HJ HARU2 Hbl2 R1 Rsp R3 R4 R10 R11 R12 R8 R9 R18 R19 R21 Rcs PF Hbytes.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fs_segs_low as HSL. pose proof fs_wx as HWX.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (FS : STK_past_nul = 64 + 16384) by reflexivity.
assert (Hnew : In (res, n + 18) (ablocks B ly2 S2)) by (rewrite Hbl2; apply in_or_app; right; left; reflexivity).
pose proof (al_blocks _ _ LAWS ly2 S2 W2 (unpoison U memT) mdc res (n + 18) HAR2 Hnew)
  as (Hres16 & Hres4096 & Hresc & Hresapp & Hrespres & Hpw & _).
assert (Hreq : req_size (n + 18) = n + 18) by (unfold req_size; destruct (n + 18 =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | reflexivity]).
rewrite Hreq in Hresc, Hrespres.
assert (Hdisj : forall b m, In (b, m) (ablocks B ly S) -> zdisjoint (b, req_size m) (res, n + 18)).
{ intros b m Hb. apply in_split in Hb as (l1 & l2 & Ebq).
  pose proof (sep_blocks_pos tfibsegs B LAWS ly2 S2 W2 _ mdc (b, m) (res, n + 18) l1 l2 [] HAR2
    ltac:(rewrite Hbl2, Ebq, <- app_assoc; reflexivity)) as Hd.
  unfold zdisjoint, block_rng in *. cbn [fst snd] in *. rewrite Hreq in Hd. exact Hd. }
assert (Hush : forall x, res <= x < res + (n + 18) -> in_ush U (bv_unsigned (Z_to_bv 64 (shadow_addr x))) = false).
{ intros x Hx. apply (pn_ush_new ly S U W mem md res (n + 18) x HARU Hdisj Hx). lia. }
assert (Hnotold : ~ In (res, n + 18) (ablocks B ly S)).
{ intros Hin. specialize (Hdisj _ _ Hin). unfold zdisjoint in Hdisj. cbn [fst snd] in Hdisj. rewrite Hreq in Hdisj. lia. }
assert (Happ : forall a, res <= a < res + (n + 18) -> 0 <= a < 2 ^ 64 /\ (a < SHADOW_OFF \/ kHighMemBeg <= a)).
{ intros a Ha. unfold in_app, kLowShadowBeg, ASAN_CEIL in Hresapp. unfold SHADOW_OFF. lia. }
assert (Hraok : ret_ok (getr regsT 1)) by (rewrite R1; apply ret_ok_even; rewrite unsigned_lit_small by (unfold RA_PN_MEMSET; lia); reflexivity).
pose proof (fsw_ecall_preU_at (SK := SKA) B STK_past_nul (spZ regs) [] ly S W (unpoison U mem) md [] ly2 S2 U W2 memT mdc 1 regsT (-64)
  HJ HARU2 ltac:(lia) eq_refl ltac:(lia) ltac:(unfold ESTACK; lia) Hraok R3 R4) as HPRE.
assert (HMS := FR_MEMSET ly2 S2 U W2 regsT memT mdc (res + n) 0 17 HPRE R10 R11 R12 ltac:(lia) ltac:(lia) ltac:(lia)).
assert (Hblk : forall m md', ARU tfibsegs B ly2 S2 U W2 m md' -> forall a, res <= a < res + (n + 18) ->
  apresent (w_H W2) m a /\ ~ aowned B ly2 S2 a).
{ intros m md' Hm a Ha.
  pose proof (al_blocks _ _ LAWS ly2 S2 W2 (unpoison U m) md' res (n + 18) (proj1 Hm) Hnew) as (_ & _ & _ & _ & Hp & _).
  rewrite Hreq in Hp. destruct (Hp a Ha) as [(Hh & b & Hb) Hno]. split; [|exact Hno].
  split; [exact Hh|]. exists b. rewrite <- (pn_unp_app ly2 S2 U W2 m md' a Hm (proj1 (Happ a Ha)) (proj2 (Happ a Ha))). exact Hb. }
assert (Hra_new : forall m md' a len, ARU tfibsegs B ly2 S2 U W2 m md' -> res <= a -> a + len <= res + (n + 18) ->
  range_addressable (aview tfibsegs (w_H W2) m) SHADOW_OFF a len).
{ intros m md' a len Hm H1 H2. apply (pn_ra_raw ly2 S2 U W2 m md' res (n + 18) a len Hm Hnew H1 ltac:(rewrite Hreq; lia)).
  intros x Hx. apply Hush. lia. }
assert (Hhull_new : forall m md' a len, ARU tfibsegs B ly2 S2 U W2 m md' -> res <= a -> a + len <= res + (n + 18) -> 0 < len ->
  shadow_hull_vis (aview tfibsegs (w_H W2) m) a len).
{ intros m md' a len Hm H1 H2 H3. apply (pn_hull_raw ly2 S2 U W2 m md' a len Hm).
  exact (shadow_hull_vis_of_block tfibsegs B LAWS ly2 S2 W2 (unpoison U m) md' res (n + 18) a len (proj1 Hm) Hnew H1
    ltac:(rewrite Hreq; lia) H3). }
specialize (HMS ltac:(intros a Ha; destruct (Hblk memT mdc HARU2 a ltac:(lia)) as [Hp Hno];
    split; [exact (apresent_writable tfibsegs _ _ _ Hp) | split; [exact Hno | rewrite Rsp; unfold ESTACK; lia]])
  (amem_range_of_block tfibsegs B LAWS ly2 S2 W2 _ mdc res (n + 18) (res + n) 17 HAR2 Hnew ltac:(lia) ltac:(rewrite Hreq; lia))
  (Hra_new memT mdc (res + n) 17 HARU2 ltac:(lia) ltac:(lia))
  (fun _ => Hhull_new memT mdc (res + n) 17 HARU2 ltac:(lia) ltac:(lia) ltac:(lia)) I).
set (Wr := fun a => (res + n <= a < res + n + 17) \/ (spZ regs - 64 - ESTACK <= a < spZ regs - 64)).
(* __asan_memset's write window is a byte of the new (temporary, not-yet-entry) block or the callee's stack window *)
assert (HW : forall a, Wr a ->
  awr_byte tfibsegs B STK_past_nul (spZ regs) [] (ablocks B ly S) (ablocks B ly2 S2) ly2 [] (frames S) a).
{ intros a [Ha|Ha].
  - left. right. right. left. exists res, (n + 18). split; [exact Hnew|]. split; [exact Hnotold|]. rewrite Hreq. lia.
  - left. left. unfold ESTACK in Ha. lia. }
eapply SRr_bind;
  first
  [ lazymatch goal with |- SRr _ _ _ _ =>
      apply (fsw_intrin_atU (SK := SKA) B STK_past_nul (spZ regs) [] ly S W (unpoison U mem) md [] ly2 S2 U W2 memT mdc 1 U Wr
        (getr regsT 1) _
        (fun regs' mem' md' => aregs_preserved regsT regs' /\ getr regs' 10 = w64 (res + n) /\
           (forall i, 0 <= i < 17 -> aview tfibsegs (w_H W2) mem' (res + n + i) = Some 0) /\
           (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview tfibsegs (w_H W2) mem' a = aview tfibsegs (w_H W2) memT a)) HJ);
      first [ lazymatch goal with |- forall _, Wr _ -> _ => solve [exact HW] end
            | lazymatch goal with |- SRr _ _ _ _ => idtac end ] end
  | lazymatch goal with |- forall _, _ => idtac end ].
(* the intrinsic's own step: the memset contract HMS, its post read as fsw_intrin_atU's *)
{ eapply SRr_mono; first [ solve [exact HMS] | lazymatch goal with |- forall _, _ => idtac end ].
  intros W' c' _ (-> & regs' & mem' & md' & -> & HARU' & HP' & Hsb & H10' & Hset & Hfr & Hgr).
  split; [reflexivity|]. exists regs', mem', md'.
  split; [unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
  assert (HfrW : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview tfibsegs (w_H W2) mem' a = aview tfibsegs (w_H W2) memT a).
  { intros a Ha HnW. apply Hfr;
      first [ solve [exact Ha] | solve [intros X; apply HnW; left; exact X]
            | solve [intros X; apply HnW; right; rewrite Rsp in X; lia] ]. }
  split; [exact HARU'|]. split; [exact Hsb|].
  split.
  { intros a Ha HnW. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Ei; [apply aview_unpoison_in; exact Ei|].
    rewrite !(aview_unpoison_out tfibsegs _ U _ a Ei). exact (HfrW a Ha HnW). }
  split.
  { intros a (Hh & b & Hb). split; [exact Hh|].
    destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Ei; [rewrite unpoison_in by exact Ei; eexists; reflexivity|].
    rewrite unpoison_out in Hb |- * by exact Ei. exact (proj2 (Hgr a (conj Hh (ex_intro _ b Hb)))). }
  split; [exact HP'|]. split; [exact H10'|]. split; [|exact HfrW].
  intros i Hi. rewrite (Hset i Hi). reflexivity. }
intros W3 c3 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HARU4 & HP4 & H104 & Hset4 & Hfr4).
rewrite R1.
assert (PF4 : pn_frame (w_H W2) mem4 (spZ regs) regs).
{ apply (pn_frame_kept _ _ _ _ _ regs PF). intros a Ha. apply Hfr4; [lia|]. unfold Wr, ESTACK. lia. }
assert (Esp4 : getr regs4 2 = getr regsT 2) by exact (HP4 2 ltac:(unfold acallee_saved; lia)).
assert (Usp4 : spZ regs4 = spZ regs - 64) by (unfold spZ at 1; rewrite Esp4; change (bv_unsigned (getr regsT 2)) with (spZ regsT); lia).
set (E4 := Ereg regs4 (fs_extraT ++ pn_xs regs)).
assert (G18 : ew E4 18 = Z_to_bv 64 (res + n)).
{ subst E4. rewrite (ew_Ereg_nat regs4 _ 18 18%bv eq_refl), (fsw_pres _ _ 18%bv HP4 ltac:(pn_csv)). exact R18. }
assert (G19 : ew E4 19 = Z_to_bv 64 (res + n + 17)).
{ subst E4. rewrite (ew_Ereg_nat regs4 _ 19 19%bv eq_refl), (fsw_pres _ _ 19%bv HP4 ltac:(pn_csv)). exact R19. }
assert (G21 : ew E4 21 = Z_to_bv 64 SHADOW_OFF).
{ subst E4. rewrite (ew_Ereg_nat regs4 _ 21 21%bv eq_refl), (fsw_pres _ _ 21%bv HP4 ltac:(pn_csv)). exact R21. }
assert (E2c : bv_unsigned (ew E4 2) = spZ regs - 64) by (subst E4; rewrite (ew_Ereg_nat regs4 _ 2 2%bv eq_refl); exact Usp4).
assert (Hout_img : res + (n + 18) <= 0x10000 \/ 0x5fd000 <= res).
{ destruct (Z_le_gt_dec (res + (n + 18)) 0x10000) as [|H1]; [left; lia|].
  destruct (Z_le_gt_dec 0x5fd000 res) as [|H2]; [right; lia|]. exfalso.
  destruct (al_client_img _ _ LAWS ly2 S2 W2 _ mdc (Z.max res 0x10000) HAR2) as [_ Hni].
  - left. exists res, (n + 18). split; [exact Hnew|]. rewrite Hreq. lia.
  - apply Hni. apply AD1y.in_img_hull. lia. }
pose proof (fsw_resume_after_rtU_args_chunks (SK := SKA) B STK_past_nul (spZ regs) [] ly S W (unpoison U mem) md [] ly2 S2 U W2
  mem4 md4 1 regs4 64 (pn_xs regs) pn_cs pn_rs pn_gf RA_PN_MEMSET HGOT HCELL HJ4 HARU4 Usp4 ltac:(lia) ltac:(lia) eq_refl
  ltac:(vm_compute; reflexivity) (pn_frame_cs _ _ _ regs regs4 PF4)) as HS5.
assert (U18 : bv_unsigned (ew E4 18) = res + n) by (rewrite G18; apply wz; lia).
assert (U19 : bv_unsigned (ew E4 19) = res + n + 17) by (rewrite G19; apply wz; lia).
assert (U21 : bv_unsigned (ew E4 21) = SHADOW_OFF) by (rewrite G21; apply wz; unfold SHADOW_OFF; lia).
fold E4 in HS5.
assert (RS5 : Forall (region_ok tfibsegs E4 (mrestrict (w_H W2) mem4)) pn_rs).
{ unfold pn_rs. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  all: unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  all: rewrite ?U18, ?U19.
  all: split; [lia|]; split; [lia|]; split; [|apply Forall_nil].
  all: intros o Ho; apply (apresent_writable tfibsegs); refine (proj1 (Hblk mem4 md4 HARU4 _ _)); lia. }
assert (PD5 : pairwise_disjoint E4 (fsT_ret_regions 64 pn_cs pn_rs)).
{ apply pairwise_disjoint_of_extents.
  unfold fsT_ret_regions, pn_rs, fstk_ret, fs_got_region, fs_bcell_region, extent_of_region.
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2c, U18, U19.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
assert (AO5 : atoms_ok E4 pn_gf).
{ unfold pn_gf. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U18, U19, U21. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF. repeat split; try lia; exact I. }
specialize (HS5 RS5 PD5 AO5).
(* the shadow entries of the three inline store checks: range_addressable on the machine's memory, so the token run
   decides each check's `bne` (0x827b0 / 0x827c8 / 0x827e0) untaken and never reaches __asan_report_store1 *)
assert (SHOK : sh_ok tfibsegs pn_Bx pn_SH E4 (mrestrict (w_H W2) mem4)).
{ assert (UB : YP0e.U E4 pn_Bx = SHADOW_OFF) by (unfold pn_Bx; apply (U_atom _ 21 SHADOW_OFF G21); unfold SHADOW_OFF; lia).
  assert (V18 : YP0e.U E4 (SOff 18 0) = res + n) by (apply (U_atom _ 18 (res + n) G18); lia).
  assert (V19 : YP0e.U E4 (SOff 19 0) = res + n + 17) by (apply (U_atom _ 19 (res + n + 17) G19); lia).
  unfold sh_ok, pn_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold shent_ok; cbn [she_m she_lo she_hi].
  - change (rd_of tfibsegs (mrestrict (w_H W2) mem4)) with (aview tfibsegs (w_H W2) mem4). rewrite UB, V18.
    split; [apply (Hra_new mem4 md4);
            first [ solve [exact HARU4] | lazymatch goal with |- (_ <= _)%Z => solve [lia] end ]|].
    unfold app_apart. cbn [she_m she_lo she_hi]. rewrite UB, V18. intros a Ha. destruct (Happ a ltac:(lia)) as [_ Ha2].
    unfold SHADOW_OFF in *. lia.
  - change (rd_of tfibsegs (mrestrict (w_H W2) mem4)) with (aview tfibsegs (w_H W2) mem4). rewrite UB, V19.
    split; [apply (Hra_new mem4 md4);
            first [ solve [exact HARU4] | lazymatch goal with |- (_ <= _)%Z => solve [lia] end ]|].
    unfold app_apart. cbn [she_m she_lo she_hi]. rewrite UB, V19. intros a Ha. destruct (Happ a ltac:(lia)) as [_ Ha2].
    unfold SHADOW_OFF in *. lia. }
fsw_aj_run_tokU pn_tbl_ok HS5 HJ4 HARU4 SHOK fs_Bspan.
{ pn_awr_ret E2c. unfold pn_rs.
  (* the two store windows: bytes of the new block *)
  eapply awr_ok_cons_gen with (k := 18%nat) (b := res + n);
    first [ lazymatch goal with |- _ = Some _ => solve [reflexivity] end
          | lazymatch goal with |- bv_unsigned _ = _ => solve [exact U18] end
          | lazymatch goal with |- forall _, _ =>
              solve [cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; right; right; left; exists res, (n + 18);
                     split; [exact Hnew|]; split; [exact Hnotold|]; rewrite Hreq; lia] end
          | pn_awr_keep ].
  eapply awr_ok_cons_gen with (k := 19%nat) (b := res + n + 17);
    first [ lazymatch goal with |- _ = Some _ => solve [reflexivity] end
          | lazymatch goal with |- bv_unsigned _ = _ => solve [exact U19] end
          | lazymatch goal with |- forall _, _ =>
              solve [cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; right; right; left; exists res, (n + 18);
                     split; [exact Hnew|]; split; [exact Hnotold|]; rewrite Hreq; lia] end
          | pn_awr_keep ].
  apply awr_ok_nil. }
set (E5 := ewset (ewset (ewset (ewset (ewset (ewset E4 40 w) 41 w0) 42 w1) 43 w2) 44 w3) 45 w4) in HS5, SHOK.
assert (EW : forall k, (k < 40)%nat -> ew E5 k = ew E4 k).
{ intros k Hk. subst E5. rewrite !ew_ewset_other by lia. reflexivity. }
assert (EX : forall j, (j < 8)%nat -> ew E4 (32 + j) = nth j (fs_extraT ++ pn_xs regs) (Z_to_bv 64 0)) by (intros j Hj; apply ew_Ereg_extra).
assert (EG : forall q : Z, (q = 3 \/ q = 4 \/ 22 <= q <= 27) -> ew E5 (Z.to_nat q) = getr regs (Z_to_bv 5 q)).
{ intros q Hq. rewrite EW by lia. subst E4. rewrite (ew_Ereg_nat regs4 _ (Z.to_nat q) (Z_to_bv 5 q)).
  - rewrite (fsw_pres _ _ (Z_to_bv 5 q) HP4); [exact (Rcs q Hq)|]. rewrite Z_to_bv_unsigned, bv_wrap_small; [unfold acallee_saved; lia|].
    unfold bv_modulus. cbn. lia.
  - rewrite Z_to_bv_unsigned, bv_wrap_small; [lia|]. unfold bv_modulus. cbn. lia. }
assert (Hjalr : v_jalr (getr (ms_regs ms) 1) 0 = getr regs 1).
{ pn_sr HS5 (1%bv : bv 5). rewrite fsw_SOff0, EW by lia. change 33%nat with (32 + 1)%nat. rewrite EX by lia. exact Hra. }
assert (HPf : aregs_preserved regs (ms_regs ms)).
{ apply (fsw_preserved _ E5 _ ms regs pn_expect HS5);
    first [ lazymatch goal with |- forallb _ _ = true => solve [vm_compute; reflexivity] end
          | lazymatch goal with |- forall _, _ => idtac end ].
  intros r Hr. cbv [CALLEE_SAVED In] in Hr.
  repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
  lazymatch goal with |- sv_denot _ (pn_expect ?q) = _ => let e := eval vm_compute in (pn_expect q) in change (pn_expect q) with e end.
  - apply bv_eq. rewrite denot_SOff, EW by lia. rewrite E2c. unfold spZ. rewrite zcanon_id; [lia|]. unfold M64.
    pose proof (u64_range (getr regs 2)). lia.
  - rewrite fsw_SOff0. exact (EG 3 ltac:(lia)).
  - rewrite fsw_SOff0. exact (EG 4 ltac:(lia)).
  - rewrite fsw_SOff0, EW by lia. change 34%nat with (32 + 2)%nat. rewrite EX by lia. reflexivity.
  - rewrite fsw_SOff0, EW by lia. change 35%nat with (32 + 3)%nat. rewrite EX by lia. reflexivity.
  - rewrite fsw_SOff0, EW by lia. change 36%nat with (32 + 4)%nat. rewrite EX by lia. reflexivity.
  - rewrite fsw_SOff0, EW by lia. change 37%nat with (32 + 5)%nat. rewrite EX by lia. reflexivity.
  - rewrite fsw_SOff0, EW by lia. change 38%nat with (32 + 6)%nat. rewrite EX by lia. reflexivity.
  - rewrite fsw_SOff0, EW by lia. change 39%nat with (32 + 7)%nat. rewrite EX by lia. reflexivity.
  - rewrite fsw_SOff0. exact (EG 22 ltac:(lia)).
  - rewrite fsw_SOff0. exact (EG 23 ltac:(lia)).
  - rewrite fsw_SOff0. exact (EG 24 ltac:(lia)).
  - rewrite fsw_SOff0. exact (EG 25 ltac:(lia)).
  - rewrite fsw_SOff0. exact (EG 26 ltac:(lia)).
  - rewrite fsw_SOff0. exact (EG 27 ltac:(lia)). }
assert (Ra10 : getr (ms_regs ms) 10 = w64 res).
{ pn_sr HS5 (10%bv : bv 5). rewrite fsw_SOff0, EW by lia. subst E4.
  rewrite (ew_Ereg_nat regs4 _ 8 8%bv eq_refl), (fsw_pres _ _ 8%bv HP4 ltac:(pn_csv)). exact R8. }
assert (U18f : base_val E5 (Some 18%nat) = res + n) by (cbn [base_val]; rewrite EW by lia; exact U18).
assert (U19f : base_val E5 (Some 19%nat) = res + n + 17) by (cbn [base_val]; rewrite EW by lia; exact U19).
pose proof (fsw_region_nth E5 _ _ 3 _ HS5 eq_refl) as HR18. cbn [ms_mem restrict] in HR18.
pose proof (fsw_region_nth E5 _ _ 4 _ HS5 eq_refl) as HR19. cbn [ms_mem restrict] in HR19.
destruct HR18 as (_ & _ & _ & HC18). destruct HR19 as (_ & _ & _ & HC19).
cbn [YP09.r_base YP09.r_chunks] in HC18, HC19.
assert (B65 : aview tfibsegs (w_H W2) (ms_mem ms) (res + n + 2) = Some 65).
{ pose proof (pn_chunk1 E5 (w_H W2) (ms_mem ms) _ 2 (SLit 65) 65 (Forall_inv HC18) eq_refl ltac:(lia)) as H.
  rewrite U18f in H. exact H. }
assert (Bc : aview tfibsegs (w_H W2) (ms_mem ms) (res + n + 1) = Some (c mod 256)).
{ assert (Dc : sv_denot E5 (SOff 9 0) = Z_to_bv 64 c).
  { rewrite fsw_SOff0, EW by lia. subst E4. rewrite (ew_Ereg_nat regs4 _ 9 9%bv eq_refl), (fsw_pres _ _ 9%bv HP4 ltac:(pn_csv)). exact R9. }
  pose proof (pn_chunk1 E5 (w_H W2) (ms_mem ms) _ 1 (SOff 9 0) c (Forall_inv (Forall_inv_tail HC18)) Dc Hc) as H.
  rewrite U18f in H. exact H. }
assert (B17 : aview tfibsegs (w_H W2) (ms_mem ms) (res + n + 17) = Some 0).
{ pose proof (pn_chunk1 E5 (w_H W2) (ms_mem ms) _ 0 (SLit 0) 0 (Forall_inv HC19) eq_refl ltac:(lia)) as H.
  rewrite U19f, Z.add_0_r in H. exact H. }
assert (NWR : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) -> ~ (res + n + 1 <= a < res + n + 3) ->
  ~ (res + n + 17 <= a < res + n + 18) -> aview tfibsegs (w_H W2) (ms_mem ms) a = aview tfibsegs (w_H W2) mem4 a).
{ intros a Ha N1 N2 N3. apply aview_at. apply HF. rewrite wz by exact Ha. intros (r & Hin & Hr).
  unfold fss_retT, fsT_ret_regions, pn_rs, fstk_ret, fs_got_region, fs_bcell_region in Hin. cbn [ss_mem app In] in Hin.
  repeat destruct Hin as [<-|Hin]; try destruct Hin;
    cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; rewrite ?E2c, ?U18, ?U19 in Hr; lia. }
(* the `ret` 0x82810 *)
eapply SRr_mono;
  first
  [ lazymatch goal with |- SRr _ _ _ _ =>
      apply (fsw_retU (SK := SKA) B pn_tbl pn_tbl_ok W2 E5 _ ms _ STK_past_nul (spZ regs) [] regs ly S U W mem md ly2 S2 U 1
        (pn_Q U ly S n c res live peak cnt fail db) HS5 eq_refl ltac:(vm_compute; reflexivity) Hjalr HJ4 HARU4 HPf) end
  | lazymatch goal with |- forall _, _ => idtac end ].
{ intros mat2. unfold pn_Q.
  split; [exact Ra10|]. split; [lia|]. split; [exact Hres16|]. split; [exact Hbl2|].
  split.
  { intros r Hr. destruct (FH r Hr) as (E16 & m & Hm & Hm16). split; [exact E16|]. exists m. split; [|exact Hm16].
    rewrite Hbl2. apply in_or_app. left. exact Hm. }
  split.
  { unfold zbytes_at. apply pn_garr8; [exact (pn_copy_bytes db c Hdb)|].
    intros j Hj. rewrite pn_copy_len in Hj.
    destruct (Nat.lt_ge_cases j (length db)) as [Hjn|Hjn].
    - rewrite pn_copy_head by exact Hjn. rewrite NWR by lia. rewrite Hfr4 by (unfold Wr, ESTACK; lia).
      replace j with (Z.to_nat (Z.of_nat j)) at 2 by lia. apply Hbytes. lia.
    - assert (Hk : exists k, j = (length db + k)%nat /\ (k < 18)%nat) by (exists (j - length db)%nat; lia).
      destruct Hk as (k & -> & Hk). rewrite pn_copy_tail by exact Hk.
      replace (res + Z.of_nat (length db + k)) with (res + n + Z.of_nat k) by lia.
      assert (Hk18 : (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/
        k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17)%nat) by lia.
      repeat destruct Hk18 as [->|Hk18]; cbn [nth app repeat Z.of_nat Pos.of_succ_nat Pos.succ].
      all: change (Z.of_nat 0) with 0; change (Z.of_nat 1) with 1; change (Z.of_nat 2) with 2; change (Z.of_nat 17) with 17.
      2: exact Bc. 2: exact B65.
      { rewrite NWR; [| lia | lia | lia | lia]. apply Hset4. lia. }
      all: try (rewrite NWR by (simpl Z.of_nat; lia); apply Hset4; simpl Z.of_nat; lia).
      subst k. exact B17. }
  apply (pn_glob_kept W W2 mem (ms_mem ms) live peak cnt fail HG).
  intros a Ha.
  assert (Hai : 0x10000 <= a < 0x5fd000).
  { destruct Ha as (rr & Hrr & Hra'). unfold FS_PSTAT_FP in Hrr. cbn [In] in Hrr.
    repeat destruct Hrr as [<-|Hrr]; try destruct Hrr; cbn [fst snd] in Hra'; lia. }
  destruct (proj1 IMG a Ha) as [Hno Hne].
  pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  rewrite <- (pn_view_app ly2 S2 U W2 (ms_mem ms) _ a HARU4) by (unfold SHADOW_OFF; lia).
  rewrite <- (pn_view_app ly S U W mem md a HARU) by (unfold SHADOW_OFF; lia).
  apply F3;
    first [ lazymatch goal with |- in_img _ _ => solve [exact (AD1y.in_img_hull a Hai)] end
          | solve [exact Hno] | solve [exact Hne]
          | lazymatch goal with |- ~ inFP _ _ => solve [intros X; exact (inFP_nil _ X)] end
          | solve [apply fp_spares_closed; exact sink_closed_nil] ]. }
intros W' c' _ Hp. exists res. exact Hp.
Qed.

Lemma pn_mid : forall ly S U (W : world tfibsegs) regs mem md n c (db : list Z) live peak cnt fail
    res ly2 S2 (W2 : world tfibsegs) regsC memC mdc d b m,
  ret_ok (getr regs 1) -> fs_heads B ly S U -> fs_glob tfibsegs W mem live peak cnt fail ->
  0 <= c < 2 ^ 64 -> 0 < n <= 2 ^ 22 -> Z.of_nat (length db) = n -> Forall (fun z => 0 <= z < 256) db ->
  ARU tfibsegs B ly S U W mem md ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF d n -> amem_range d n -> 4096 <= d -> d + n + 8 <= alloc_ceiling ->
  In (b, m) (ablocks B ly S) -> b <= d -> d + n <= b + m ->
  (forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem (d + i) = Some (nth (Z.to_nat i) db 0)) ->
  ajournal (SK := SKA) tfibsegs B STK_past_nul (spZ regs) [] ly S W (unpoison U mem) md [] ly2 S2 W2
    (unpoison U memC) mdc 1 ->
  ARU tfibsegs B ly2 S2 U W2 memC mdc ->
  ablocks B ly2 S2 = ablocks B ly S ++ [(res, n + 18)] ->
  getr regsC 1 = Z_to_bv 64 RA_PN_MEMCPY -> spZ regsC = spZ regs - 64 ->
  getr regsC 3 = w64 (as_gp B) -> getr regsC 4 = w64 (as_tp B) ->
  getr regsC 10 = w64 res -> getr regsC 11 = w64 d -> getr regsC 12 = w64 n ->
  getr regsC 8 = w64 res -> getr regsC 9 = w64 c -> getr regsC 18 = w64 n ->
  getr regsC 19 = w64 (n + 18) -> getr regsC 20 = w64 d -> getr regsC 21 = w64 SHADOW_OFF ->
  (forall q, (q = 3 \/ q = 4 \/ 22 <= q <= 27) -> getr regsC (Z_to_bv 5 q) = getr regs (Z_to_bv 5 q)) ->
  pn_frame (w_H W2) memC (spZ regs) regs ->
  SRr tfibsegs W2 (mkCfg (mkst regsC (Z_to_bv 64 PC_memcpy) memC (seg_rom tfibsegs)) mdc)
    (fun W' c' => exists res0, apost_baseU (SK := SKA) tfibsegs B STK_past_nul [] regs ly S W mem md EV_past_nul U U
       (pn_Q U ly S n c res0 live peak cnt fail db) W' c').
Proof.
intros ly S U W regs mem md n c db live peak cnt fail res ly2 S2 W2 regsC memC mdc d b m
  Hra FH HG Hc Hn Hlen Hdb HARU Hdra Hdam Hd4 Hdc Hbm Hbd Hdn Hsrc HJ HARU2 Hbl2
  R1 Rsp R3 R4 R10 R11 R12 R8 R9 R18 R19 R20 R21 Rcs PF.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fs_segs_low as HSL. pose proof fs_wx as HWX.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (FS : STK_past_nul = 64 + 16384) by reflexivity.
assert (Hnew : In (res, n + 18) (ablocks B ly2 S2)) by (rewrite Hbl2; apply in_or_app; right; left; reflexivity).
assert (Hbm2 : In (b, m) (ablocks B ly2 S2)) by (rewrite Hbl2; apply in_or_app; left; exact Hbm).
pose proof (al_blocks _ _ LAWS ly2 S2 W2 (unpoison U memC) mdc res (n + 18) HAR2 Hnew)
  as (Hres16 & Hres4096 & Hresc & Hresapp & Hrespres & Hpw & _).
pose proof (al_blocks _ _ LAWS ly2 S2 W2 (unpoison U memC) mdc b m HAR2 Hbm2)
  as (Hb16 & Hb4096 & Hbc & Hbapp & Hbpres & _ & Hbmx).
assert (Hreq : req_size (n + 18) = n + 18) by (unfold req_size; destruct (n + 18 =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | reflexivity]).
assert (Hreqm : m <= req_size m) by (unfold req_size; destruct (m =? 0) eqn:Ez; [apply Z.eqb_eq in Ez|]; lia).
rewrite Hreq in Hresc, Hrespres.
assert (Hdisj : forall b0 m0, In (b0, m0) (ablocks B ly S) -> zdisjoint (b0, req_size m0) (res, n + 18)).
{ intros b0 m0 Hb. apply in_split in Hb as (l1 & l2 & Ebq).
  pose proof (sep_blocks_pos tfibsegs B LAWS ly2 S2 W2 _ mdc (b0, m0) (res, n + 18) l1 l2 [] HAR2
    ltac:(rewrite Hbl2, Ebq, <- app_assoc; reflexivity)) as Hd.
  unfold zdisjoint, block_rng in *. cbn [fst snd] in *. rewrite Hreq in Hd. exact Hd. }
assert (Hnotold : ~ In (res, n + 18) (ablocks B ly S)).
{ intros Hin. specialize (Hdisj _ _ Hin). unfold zdisjoint in Hdisj. cbn [fst snd] in Hdisj. lia. }
assert (Hush : forall x, res <= x < res + (n + 18) -> in_ush U (bv_unsigned (Z_to_bv 64 (shadow_addr x))) = false).
{ intros x Hx. apply (pn_ush_new ly S U W mem md res (n + 18) x HARU Hdisj Hx). unfold in_app, kLowShadowBeg, ASAN_CEIL in Hresapp. lia. }
assert (Happ : forall a, res <= a < res + (n + 18) -> 0 <= a < 2 ^ 64 /\ (a < SHADOW_OFF \/ kHighMemBeg <= a)).
{ intros a Ha. unfold in_app, kLowShadowBeg, ASAN_CEIL in Hresapp. rewrite Hreq in Hresapp. unfold SHADOW_OFF. lia. }
assert (Bapp : forall a, b <= a < b + req_size m -> 0 <= a < 2 ^ 64 /\ (a < SHADOW_OFF \/ kHighMemBeg <= a)).
{ intros a Ha. unfold in_app, kLowShadowBeg, ASAN_CEIL in Hbapp. unfold SHADOW_OFF. lia. }
assert (Hsd : res + n <= d \/ d + n <= res).
{ specialize (Hdisj b m Hbm). unfold zdisjoint in Hdisj. cbn [fst snd] in Hdisj. lia. }
(* the source bytes at the call: the journal keeps the old block (b, m) *)
assert (HsrcC : forall i, 0 <= i < n -> aview tfibsegs (w_H W2) memC (d + i) = Some (nth (Z.to_nat i) db 0)).
{ intros i Hi. destruct (Bapp (d + i) ltac:(lia)) as [B1 B2].
  rewrite <- (pn_view_app ly2 S2 U W2 memC mdc (d + i) HARU2 B1 B2).
  replace (d + i) with (b + (d + i - b)) by lia.
  rewrite (F2 b m (d + i - b) Hbm Hbm2 ltac:(lia) ltac:(intros X; exact (inFP_nil _ X))).
  replace (b + (d + i - b)) with (d + i) by lia.
  rewrite (pn_view_app ly S U W mem md (d + i) HARU B1 B2). exact (Hsrc i Hi). }
assert (Hraok : ret_ok (getr regsC 1)) by (rewrite R1; apply ret_ok_even; rewrite unsigned_lit_small by (unfold RA_PN_MEMCPY; lia); reflexivity).
pose proof (fsw_ecall_preU_at (SK := SKA) B STK_past_nul (spZ regs) [] ly S W (unpoison U mem) md [] ly2 S2 U W2 memC mdc 1 regsC (-64)
  HJ HARU2 ltac:(lia) eq_refl ltac:(lia) ltac:(unfold ESTACK; lia) Hraok R3 R4) as HPRE.
assert (Hblk : forall mm md', ARU tfibsegs B ly2 S2 U W2 mm md' -> forall a, res <= a < res + (n + 18) ->
  apresent (w_H W2) mm a /\ ~ aowned B ly2 S2 a).
{ intros mm md' Hm a Ha.
  pose proof (al_blocks _ _ LAWS ly2 S2 W2 (unpoison U mm) md' res (n + 18) (proj1 Hm) Hnew) as (_ & _ & _ & _ & Hp & _).
  rewrite Hreq in Hp. destruct (Hp a Ha) as [(Hh & bb & Hb) Hno]. split; [|exact Hno].
  split; [exact Hh|]. exists bb. rewrite <- (pn_unp_app ly2 S2 U W2 mm md' a Hm (proj1 (Happ a Ha)) (proj2 (Happ a Ha))). exact Hb. }
assert (HMC := FR_MEMCPY ly2 S2 U W2 regsC memC mdc res d n HPRE R10 R11 R12 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; destruct (Hblk memC mdc HARU2 a ltac:(lia)) as [Hp Hno];
    split; [exact (apresent_writable tfibsegs _ _ _ Hp) | split; [exact Hno | rewrite Rsp; unfold ESTACK; lia]])
  (amem_range_of_block tfibsegs B LAWS ly2 S2 W2 _ mdc res (n + 18) res n HAR2 Hnew ltac:(lia) ltac:(rewrite Hreq; lia))
  (pn_ra_raw ly2 S2 U W2 memC mdc res (n + 18) res n HARU2 Hnew ltac:(lia) ltac:(rewrite Hreq; lia) ltac:(intros x Hx; apply Hush; lia))
  (fun Hn0 => pn_hull_raw ly2 S2 U W2 memC mdc res n HARU2
     (shadow_hull_vis_of_block tfibsegs B LAWS ly2 S2 W2 _ mdc res (n + 18) res n HAR2 Hnew ltac:(lia) ltac:(rewrite Hreq; lia) Hn0))).
specialize (HMC ltac:(split; [lia|]; split; [lia|]; split;
  [ intros a Ha; split; [replace a with (d + (a - d)) by lia; rewrite (HsrcC (a - d)) by lia; discriminate | rewrite Rsp; unfold ESTACK; lia]
  | split; [exact Hsd|]; split; [exact Hdam|]; split;
    [ exact (pn_ra_raw ly2 S2 U W2 memC mdc b m d n HARU2 Hbm2 Hbd ltac:(lia)
               (fun x Hx => pn_ush_src W mem U d n Hdra (proj2 (proj2 HARU)) x Hx ltac:(lia)))
    | intros Hn0; apply (pn_hull_raw ly2 S2 U W2 memC mdc d n HARU2);
      exact (shadow_hull_vis_of_block tfibsegs B LAWS ly2 S2 W2 _ mdc b m d n HAR2 Hbm2 Hbd ltac:(lia) Hn0) ] ])).
set (Wr := fun a => (res <= a < res + n) \/ (spZ regs - 64 - ESTACK <= a < spZ regs - 64)).
(* __asan_memcpy's write window is a byte of the new (temporary) block or the callee's stack window *)
assert (HW : forall a, Wr a ->
  awr_byte tfibsegs B STK_past_nul (spZ regs) [] (ablocks B ly S) (ablocks B ly2 S2) ly2 [] (frames S) a).
{ intros a [Ha|Ha].
  - left. right. right. left. exists res, (n + 18). split; [exact Hnew|]. split; [exact Hnotold|]. rewrite Hreq. lia.
  - left. left. unfold ESTACK in Ha. lia. }
eapply SRr_bind;
  first
  [ lazymatch goal with |- SRr _ _ _ _ =>
      apply (fsw_intrin_atU (SK := SKA) B STK_past_nul (spZ regs) [] ly S W (unpoison U mem) md [] ly2 S2 U W2 memC mdc 1 U Wr
        (getr regsC 1) _
        (fun regs' mem' md' => aregs_preserved regsC regs' /\
           (forall i, 0 <= i < n -> aview tfibsegs (w_H W2) mem' (res + i) = Some (nth (Z.to_nat i) db 0)) /\
           (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview tfibsegs (w_H W2) mem' a = aview tfibsegs (w_H W2) memC a)) HJ);
      first [ lazymatch goal with |- forall _, Wr _ -> _ => solve [exact HW] end
            | lazymatch goal with |- SRr _ _ _ _ => idtac end ] end
  | lazymatch goal with |- forall _, _ => idtac end ].
(* the intrinsic's own step: the memcpy contract HMC, its post read as fsw_intrin_atU's *)
{ eapply SRr_mono; first [ solve [exact HMC] | lazymatch goal with |- forall _, _ => idtac end ].
  intros W' c' _ (-> & regs' & mem' & md' & -> & HARU' & HP' & Hsb & H10' & Hcpy & Hfr & Hgr).
  split; [reflexivity|]. exists regs', mem', md'.
  split; [unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
  assert (HfrW : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview tfibsegs (w_H W2) mem' a = aview tfibsegs (w_H W2) memC a).
  { intros a Ha HnW. apply Hfr;
      first [ solve [exact Ha] | solve [intros X; apply HnW; left; exact X]
            | solve [intros X; apply HnW; right; rewrite Rsp in X; lia] ]. }
  split; [exact HARU'|]. split; [exact Hsb|].
  split.
  { intros a Ha HnW. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Ei; [apply aview_unpoison_in; exact Ei|].
    rewrite !(aview_unpoison_out tfibsegs _ U _ a Ei). exact (HfrW a Ha HnW). }
  split.
  { intros a (Hh & bb & Hb). split; [exact Hh|].
    destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Ei; [rewrite unpoison_in by exact Ei; eexists; reflexivity|].
    rewrite unpoison_out in Hb |- * by exact Ei. exact (proj2 (Hgr a (conj Hh (ex_intro _ bb Hb)))). }
  split; [exact HP'|]. split; [|exact HfrW].
  intros i Hi. rewrite (Hcpy i Hi). exact (HsrcC i Hi). }
intros W3 c3 _ (-> & regs6 & mem6 & md6 & -> & HJ6 & HARU6 & HP6 & Hcp6 & Hfr6).
rewrite R1.
assert (PF6 : pn_frame (w_H W2) mem6 (spZ regs) regs).
{ apply (pn_frame_kept _ _ _ _ _ regs PF). intros a Ha. apply Hfr6; [lia|]. unfold Wr, ESTACK. lia. }
assert (Esp6 : getr regs6 2 = getr regsC 2) by exact (HP6 2 ltac:(unfold acallee_saved; lia)).
assert (Usp6 : spZ regs6 = spZ regs - 64) by (unfold spZ at 1; rewrite Esp6; change (bv_unsigned (getr regsC 2)) with (spZ regsC); lia).
pose proof (fsw_resume_after_rtU_args_chunks (SK := SKA) B STK_past_nul (spZ regs) [] ly S W (unpoison U mem) md [] ly2 S2 U W2
  mem6 md6 1 regs6 64 (pn_xs regs) pn_cs [] [] RA_PN_MEMCPY HGOT HCELL HJ6 HARU6 Usp6 ltac:(lia) ltac:(lia) eq_refl
  ltac:(vm_compute; reflexivity) (pn_frame_cs _ _ _ regs regs6 PF6) (Forall_nil _)) as HS6.
set (E6 := Ereg regs6 (fs_extraT ++ pn_xs regs)) in HS6.
assert (E6b : bv_unsigned (ew E6 2) = spZ regs - 64) by (subst E6; rewrite (ew_Ereg_nat regs6 _ 2 2%bv eq_refl); exact Usp6).
specialize (HS6 ltac:(apply pairwise_disjoint_of_extents;
  unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, extent_of_region;
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite E6b;
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address;
  cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
  repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia]) I).
assert (G6 : forall (k : nat) (r : bv 5) v, Z.of_nat k = bv_unsigned r -> acallee_saved (bv_unsigned r) ->
  getr regsC r = Z_to_bv 64 v -> ew E6 k = Z_to_bv 64 v).
{ intros k r v Hk Hr Hv. subst E6. rewrite (ew_Ereg_nat regs6 _ k r Hk), (fsw_pres _ _ r HP6 Hr). exact Hv. }
assert (V8 : ew E6 8 = Z_to_bv 64 res) by exact (G6 8%nat 8%bv res eq_refl ltac:(pn_csv) R8).
assert (V9 : ew E6 9 = Z_to_bv 64 c) by exact (G6 9%nat 9%bv c eq_refl ltac:(pn_csv) R9).
assert (V18 : ew E6 18 = Z_to_bv 64 n) by exact (G6 18%nat 18%bv n eq_refl ltac:(pn_csv) R18).
assert (V19 : ew E6 19 = Z_to_bv 64 (n + 18)) by exact (G6 19%nat 19%bv (n + 18) eq_refl ltac:(pn_csv) R19).
assert (V21 : ew E6 21 = Z_to_bv 64 SHADOW_OFF) by exact (G6 21%nat 21%bv SHADOW_OFF eq_refl ltac:(pn_csv) R21).
assert (VQ : forall q : nat, (q = 3 \/ q = 4 \/ 22 <= q <= 27)%nat -> ew E6 q = getr regs (Z_to_bv 5 (Z.of_nat q))).
{ intros q Hq. subst E6.
  assert (Hu : Z.of_nat q = bv_unsigned (Z_to_bv 5 (Z.of_nat q))) by (rewrite Z_to_bv_unsigned, bv_wrap_small; [lia|]; unfold bv_modulus; cbn; lia).
  rewrite (ew_Ereg_nat regs6 _ q _ Hu), (fsw_pres _ _ _ HP6) by (rewrite <- Hu; unfold acallee_saved; lia).
  apply Rcs. lia. }
assert (EX6 : forall j, (j < 8)%nat -> ew E6 (32 + j) = nth j (fs_extraT ++ pn_xs regs) (Z_to_bv 64 0)) by (intros j Hj; apply ew_Ereg_extra).
fsw_aj_runU pn_tbl_ok HS6 HJ6 HARU6.
{ pn_awr_ret E6b. apply awr_ok_nil. }
lazymatch type of HS6 with st_ok _ _ _ (restrict _ ?mm) => rename mm into msM end.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W2) E6 _ msM HS6 eq_refl). cbn [ss_pc]. change 336316 with PC_memset.
assert (HbytesM : forall i, 0 <= i < n -> aview tfibsegs (w_H W2) (ms_mem msM) (res + i) = Some (nth (Z.to_nat i) db 0)).
{ intros i Hi. rewrite <- (Hcp6 i Hi). apply aview_at. apply HF. rewrite wz by lia. intros (rr & Hin & Hr).
  unfold fss_retT, fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region in Hin. cbn [ss_mem app In] in Hin.
  repeat destruct Hin as [<-|Hin]; try destruct Hin;
    cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; rewrite ?E6b in Hr; lia. }
(* the __asan_memset call and everything after it *)
eapply SRr_mono;
  first
  [ lazymatch goal with |- SRr _ _ _ _ =>
      eapply (pn_tail ly S U W regs mem md n c db live peak cnt fail res ly2 S2 W2 (ms_regs msM) (ms_mem msM) _
        Hra FH HG Hc ltac:(lia) Hlen Hdb HARU HJ6 HARU6 Hbl2);
      first
      [ lazymatch goal with |- getr _ _ = Z_to_bv 64 RA_PN_MEMSET =>
          solve [exact (fsw_reg_lit _ E6 _ msM 1%bv RA_PN_MEMSET HS6 ltac:(clear; vm_compute; reflexivity)
                          ltac:(clear; unfold RA_PN_MEMSET; lia))] end
      | lazymatch goal with |- spZ _ = _ => solve [unfold spZ at 1; pn_sr HS6 (2%bv : bv 5); rewrite fsw_SOff0; exact E6b] end
      | lazymatch goal with |- getr _ ?q = w64 (as_gp B) =>
          solve [pn_sr HS6 q; rewrite fsw_SOff0, (VQ 3%nat ltac:(lia));
                 transitivity (getr regsC 3); [symmetry; exact (Rcs 3 ltac:(lia)) | exact R3]] end
      | lazymatch goal with |- getr _ ?q = w64 (as_tp B) =>
          solve [pn_sr HS6 q; rewrite fsw_SOff0, (VQ 4%nat ltac:(lia));
                 transitivity (getr regsC 4); [symmetry; exact (Rcs 4 ltac:(lia)) | exact R4]] end
      | lazymatch goal with |- getr _ ?q = w64 _ => solve [pn_val HS6 q E6] end
      | lazymatch goal with |- pn_frame _ _ _ _ =>
          solve [pose proof (fsw_region_nth E6 _ _ 0 _ HS6 eq_refl) as HR; cbn [ms_mem restrict] in HR;
                 exact (pn_frame_of_cs E6 _ _ _ regs EX6 E6b HR)] end
      | lazymatch goal with |- forall _, _ -> aview _ _ _ _ = _ => solve [exact HbytesM] end
      | lazymatch goal with |- forall _, _ -> getr _ _ = getr _ _ => solve [pn_rcsv HS6 VQ] end ] end
  | lazymatch goal with |- forall _, _ => idtac end ].
intros W' c' _ Hp. exact Hp.
Qed.

Theorem past_nul_ok : @past_nul_spec fx rc AE2k.tfib_sink_head tfibsegs B.
Proof.
intros ly S U W regs mem md ch d n c db live peak cnt fail HPRE FH H10 H11 H12 Hc Hn Hlen HSRC HBLK HG HQ Hev Hlv Hmx.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fs_segs_low as HSL. pose proof fs_wx as HWX.
destruct HPRE as [HAPU HRO]. destruct FR_MALLOC as [HMPC AMALLOC].
pose proof (fsw_sp B _ ly S U W regs mem md ch HAPU) as (Hal16 & Hceil & H47 & HS0).
pose proof (fsw_ARU B _ ly S U W regs mem md ch HAPU) as HARU.
pose proof HARU as HARU0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HAPU as (HAP & HOK & HPO).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
assert (FS : STK_past_nul = 64 + 16384) by reflexivity.
pose proof (fsw_entryT B STK_past_nul 64 ly S U W regs mem md ch A_past_nul HGOT HCELL HAPU ltac:(lia) ltac:(vm_compute; reflexivity)) as HS.
pose proof (ajournal_init (SK := SKA) tfibsegs B STK_past_nul [] ly S W regs (unpoison U mem) md ch HAP) as HJ.
set (E := Ereg regs fs_extraT) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity).
unfold cfg_at. change (w64 A_past_nul) with (Z_to_bv 64 A_past_nul).
fsw_aj_run_toU pn_tbl_ok HS HJ HARU PC_malloc.
{ unfold fss0T, fsT_regions; cbn [ss_mem].
  eapply awr_ok_cons_stack with (n := 2%nat); first [ solve [pn_awr_side Usp] | pn_awr_keep ].
  pn_awr_cells Usp. apply awr_ok_nil. }
(* ---- the call of __wrap_malloc at 0x82768 ---- *)
pose proof (fsw_reg_lit _ E _ ms 1%bv RA_PN_MALLOC HS ltac:(vm_compute; reflexivity) ltac:(unfold RA_PN_MALLOC; lia)) as R1.
pose proof (fsw_reg_off _ E _ ms 2%bv 2 (-64) (spZ regs) HS ltac:(vm_compute; reflexivity) Usp ltac:(lia)) as R2.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl) as R3.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl) as R4.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms 8%bv 8%bv 8 HS ltac:(vm_compute; reflexivity) eq_refl) as R8.
assert (U11 : bv_unsigned (ew E 11) = n).
{ subst E. rewrite (ew_Ereg_nat regs fs_extraT 11 11%bv eq_refl), H11. unfold w64. apply wz. lia. }
pose proof (fsw_reg_off _ E _ ms 10%bv 11 18 n HS ltac:(vm_compute; reflexivity) U11 ltac:(lia)) as R10.
assert (Hspc : spZ (ms_regs ms) = spZ regs + -64) by (unfold spZ at 1; rewrite R2; lia).
assert (U12 : bv_unsigned (ew E 12) = c).
{ subst E. rewrite (ew_Ereg_nat regs fs_extraT 12 12%bv eq_refl), H12. unfold w64. apply wz. lia. }
assert (U10 : bv_unsigned (ew E 10) = d).
{ subst E. rewrite (ew_Ereg_nat regs fs_extraT 10 10%bv eq_refl), H10. unfold w64. apply wz.
  destruct HSRC as (_ & Hd4 & Hdc & _). lia. }
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF).
{ subst E. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. apply wz. unfold SHADOW_OFF. lia. }
pose proof (fsw_reg_off _ E _ ms 9%bv 12 0 c HS ltac:(vm_compute; reflexivity) U12 ltac:(lia)) as R9.
pose proof (fsw_reg_off _ E _ ms 18%bv 11 0 n HS ltac:(vm_compute; reflexivity) U11 ltac:(lia)) as R18.
pose proof (fsw_reg_off _ E _ ms 19%bv 11 18 n HS ltac:(vm_compute; reflexivity) U11 ltac:(lia)) as R19.
pose proof (fsw_reg_off _ E _ ms 20%bv 10 0 d HS ltac:(vm_compute; reflexivity) U10 ltac:(destruct HSRC as (_ & Hd4 & Hdc & _); lia)) as R20.
pose proof (fsw_reg_off _ E _ ms 21%bv 32 0 SHADOW_OFF HS ltac:(vm_compute; reflexivity) U32 ltac:(unfold SHADOW_OFF; lia)) as R21.
(* the callee-saved registers the entry run left as their entry atoms, as closed terms (no open goal reaches the
   vm_compute of the register lookups) *)
assert (RQ : forall q : nat, (q = 3 \/ q = 4 \/ 22 <= q <= 27)%nat ->
  getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat q)) = getr regs (Z_to_bv 5 (Z.of_nat q))).
{ intros q Hq.
  assert (Hq' : q = 3%nat \/ q = 4%nat \/ q = 22%nat \/ q = 23%nat \/ q = 24%nat \/ q = 25%nat \/ q = 26%nat \/ q = 27%nat) by lia.
  destruct Hq' as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]];
  lazymatch type of HS with st_ok _ _ ?ss0 (restrict ?H0 _) =>
  lazymatch goal with |- getr _ (Z_to_bv 5 (Z.of_nat ?k)) = _ =>
    exact (fsw_reg_atom H0 regs fs_extraT ss0 ms (Z_to_bv 5 (Z.of_nat k)) (Z_to_bv 5 (Z.of_nat k)) k HS
             ltac:(clear; vm_compute; reflexivity) ltac:(clear; vm_compute; reflexivity)) end end. }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms HS eq_refl). cbn [ss_pc]. change 340084 with PC_malloc. rewrite <- HMPC.
(* fsw_aj_malloc04U: its event room st_nev S < EV_MAX is the spec's budget (EV_past_nul = 1); the kit discharges the
   realizer's trace disjunct by the second arm from it *)
eapply SRr_bind;
  first
  [ lazymatch goal with |- SRr _ _ _ _ =>
      apply (fsw_aj_malloc04U (SK := SKA) B FS_ENV ML AMALLOC W (ms_regs ms) (ms_mem ms) STK_past_nul (spZ regs) [] ly S W mem md [] ly S U
        (with_vm_backing (m_vm_lazy md) mat md) 0 (n + 18) (-64) (Z_to_bv 64 RA_PN_MALLOC) ch HJ HARU);
      first
      [ lazymatch goal with |- getr _ _ = w64 (as_gp B) => solve [rewrite R3; exact Hgp] end
      | lazymatch goal with |- getr _ _ = w64 (as_tp B) => solve [rewrite R4; exact Htp] end
      | lazymatch goal with |- getr _ _ = w64 _ => solve [unfold w64; rewrite <- R10; symmetry; apply Z_to_bv_bv_unsigned] end
      | lazymatch goal with |- getr _ _ = Z_to_bv 64 _ => solve [exact R1] end
      | lazymatch goal with |- YK0s.ret_ok _ =>
          solve [apply ret_ok_even; rewrite unsigned_lit_small by (unfold RA_PN_MALLOC; lia); reflexivity] end
      | lazymatch goal with |- @eq Z (spZ _) _ => solve [exact Hspc] end
      | lazymatch goal with |- @eq Z (_ mod _) _ => solve [reflexivity] end
      | lazymatch goal with |- (blocks_bytes _ + _ <= _)%Z => solve [exact Hlv] end
      | lazymatch goal with |- (st_nev _ < _)%Z => solve [unfold EV_past_nul in Hev; lia] end
      | lazymatch goal with |- (_ <= _ < _)%Z => solve [unfold MALLOC_MAX in *; lia] end
      | lazymatch goal with |- (_ <= _)%Z => solve [lia | unfold ASTACK; lia] end
      | lazymatch goal with |- chain_pre _ _ _ _ =>
          solve
          [ apply (achain_chain_pre ly _ (spZ regs) (s0Z regs) ch (ms_regs ms));
            first
            [ lazymatch goal with |- achain _ _ _ _ _ =>
                apply (achain_kept ly (aview tfibsegs (w_H W) (unpoison U mem)) _ (spZ regs) (s0Z regs) ch (spZ regs) Hch ltac:(lia));
                first
                [ lazymatch goal with |- (_ <= _)%Z =>
                    solve [pose proof Hstk as (_ & _ & _ & _ & Hshi & Hshi47 & _ & _ & Htop2); lia] end
                | lazymatch goal with |- forall _, _ =>
                    solve [intros a Ha; pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; lia] end ] end
            | lazymatch goal with |- (_ <= _ <= _)%Z => solve [lia] end
            | lazymatch goal with |- @eq Z (s0Z _) _ => solve [unfold s0Z; rewrite R8; reflexivity] end
            | lazymatch goal with |- (_ <= raZ _)%Z =>
                solve [unfold raZ; rewrite R1, unsigned_lit_small by (unfold RA_PN_MALLOC; lia); unfold RA_PN_MALLOC; lia] end ] ] end ] end
  | lazymatch goal with |- forall _, _ => idtac end ].
intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HARU2 & HJ2 & HP2 & H10r & Hfr2 & Hres & Hbl2 & HK2).
(* ---- back at 0x8276c ---- *)
pose proof (fsw_region_nth E _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
pose proof (pn_frame_of_entry regs (w_H W) (ms_mem ms) (spZ regs) HR0 Usp) as PF1. clear HR0.
pose proof HK2 as (K1 & K2 & K3 & K4 & K5 & K6).
assert (HSA : forall a, spZ regs - 64 <= a < spZ regs ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W) (ms_mem ms) a).
{ intros a Ha.
  rewrite <- (fsw_aview_unpoison_high B ly2 S2 U W2 mem2 md2 a HARU2) by lia.
  rewrite <- (fsw_aview_unpoison_high B ly S U W (ms_mem ms) _ a HARU) by lia.
  apply K1; lia. }
pose proof (pn_frame_kept _ (w_H W2) _ mem2 _ regs PF1 HSA) as PF2.
assert (Esp2 : getr regs2 2 = getr (ms_regs ms) 2) by exact (HP2 2 ltac:(unfold acallee_saved; lia)).
assert (Usp2 : spZ regs2 = spZ regs - 64) by (unfold spZ at 1; rewrite Esp2; change (bv_unsigned (getr (ms_regs ms) 2)) with (spZ (ms_regs ms)); lia).
pose proof (fsw_resume_after_rtU_args_chunks (SK := SKA) B STK_past_nul (spZ regs) [] ly S W (unpoison U mem) md [] ly2 S2 U W2 mem2 md2 (0 + 1)
  regs2 64 (pn_xs regs) pn_cs [] [] RA_PN_MALLOC HGOT HCELL HJ2 HARU2 Usp2 ltac:(lia) ltac:(lia) eq_refl ltac:(vm_compute; reflexivity)
  (pn_frame_cs _ _ _ regs regs2 PF2) (Forall_nil _)) as HS2.
assert (Hnew : In (res, n + 18) (ablocks B ly2 S2)) by (rewrite Hbl2; apply in_or_app; right; left; reflexivity).
pose proof (al_blocks _ _ LAWS ly2 S2 W2 (unpoison U mem2) md2 res (n + 18) (proj1 HARU2) Hnew)
  as (Hres16 & _ & Hresc & Hresapp & Hrespres & Hpw & _).
assert (Hreq : req_size (n + 18) = n + 18) by (unfold req_size; destruct (n + 18 =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | reflexivity]).
rewrite Hreq in Hresc, Hrespres.
assert (E2b : bv_unsigned (ew (Ereg regs2 (fs_extraT ++ pn_xs regs)) 2) = spZ regs - 64)
  by (rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl); exact Usp2).
specialize (HS2 ltac:(apply pairwise_disjoint_of_extents;
  unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, extent_of_region;
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite E2b;
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address;
  cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
  repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia]) I).
set (E2 := Ereg regs2 (fs_extraT ++ pn_xs regs)) in HS2, E2b.
assert (E10 : ew E2 10 = Z_to_bv 64 res) by (subst E2; rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl); exact H10r).
fsw_aj_runU pn_tbl_ok HS2 HJ2 HARU2.
{ pn_awr_ret E2b. apply awr_ok_nil. }
(* `beqz a0` 0x8276c: the NULL arm (-> __asan_handle_no_return, abort) is refuted, res >= 4096 *)
eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 10 0) (b := SLit 0);
  first
  [ solve [exact HS2]
  | lazymatch goal with |- branch_taken _ _ _ = true -> _ =>
      solve [intros Hb _; exfalso; rewrite branch_eq_U, (U_atom _ 10 res E10 ltac:(lia)), U_lit in Hb by lia;
             apply Z.eqb_eq in Hb; lia] end
  | lazymatch goal with |- branch_taken _ _ _ = false -> _ => idtac end ].
intros _ HS3. clear HS2.
(* ---- the atoms of the post-malloc env E2 ---- *)
assert (VQ : forall q : nat, (q = 3 \/ q = 4 \/ 22 <= q <= 27)%nat -> ew E2 q = getr regs (Z_to_bv 5 (Z.of_nat q))).
{ intros q Hq. subst E2.
  assert (Hu : Z.of_nat q = bv_unsigned (Z_to_bv 5 (Z.of_nat q))) by (rewrite Z_to_bv_unsigned, bv_wrap_small; [lia|]; unfold bv_modulus; cbn; lia).
  rewrite (ew_Ereg_nat regs2 _ q _ Hu), (fsw_pres _ _ _ HP2) by (rewrite <- Hu; unfold acallee_saved; lia). exact (RQ q Hq). }
assert (V9 : ew E2 9 = Z_to_bv 64 c).
{ subst E2. rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl), (fsw_pres _ _ 9%bv HP2 ltac:(pn_csv)).
  apply bv_eq. rewrite R9, unsigned_lit_small by lia. lia. }
assert (V18 : ew E2 18 = Z_to_bv 64 n).
{ subst E2. rewrite (ew_Ereg_nat regs2 _ 18 18%bv eq_refl), (fsw_pres _ _ 18%bv HP2 ltac:(pn_csv)).
  apply bv_eq. rewrite R18, unsigned_lit_small by lia. lia. }
assert (V19 : ew E2 19 = Z_to_bv 64 (n + 18)).
{ subst E2. rewrite (ew_Ereg_nat regs2 _ 19 19%bv eq_refl), (fsw_pres _ _ 19%bv HP2 ltac:(pn_csv)).
  apply bv_eq. rewrite R19, unsigned_lit_small by lia. lia. }
assert (V20 : ew E2 20 = Z_to_bv 64 d).
{ subst E2. rewrite (ew_Ereg_nat regs2 _ 20 20%bv eq_refl), (fsw_pres _ _ 20%bv HP2 ltac:(pn_csv)).
  destruct HSRC as (_ & Hd4 & Hdc & _). apply bv_eq. rewrite R20, unsigned_lit_small by lia. lia. }
assert (V21 : ew E2 21 = Z_to_bv 64 SHADOW_OFF).
{ subst E2. rewrite (ew_Ereg_nat regs2 _ 21 21%bv eq_refl), (fsw_pres _ _ 21%bv HP2 ltac:(pn_csv)).
  apply bv_eq. rewrite R21, unsigned_lit_small by (unfold SHADOW_OFF; lia). lia. }
assert (EX2 : forall j, (j < 8)%nat -> ew E2 (32 + j) = nth j (fs_extraT ++ pn_xs regs) (Z_to_bv 64 0)) by (intros j Hj; apply ew_Ereg_extra).
pose proof HSRC as (HZB & Hd4 & Hdc & Hdam & Hdra & Hdhull).
pose proof (garr8_bytes_ok tfibsegs _ _ _ HZB) as Hdb.
assert (Hsrc0 : forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem (d + i) = Some (nth (Z.to_nat i) db 0)).
{ intros i Hi. replace (d + i) with (d + Z.of_nat (Z.to_nat i)) by lia. apply pn_aview_of_garr8; [exact HZB | lia]. }
fsw_aj_runU pn_tbl_ok HS3 HJ2 HARU2.
{ pn_awr_ret E2b. apply awr_ok_nil. }
(* `beqz s2` 0x82774: n = 0 skips the copy. Each case refutes the other arm by exfalso. *)
destruct (Z.eq_dec n 0) as [Hn0 | Hn0].
- eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 18 0) (b := SLit 0);
    first
    [ solve [exact HS3]
    | lazymatch goal with |- branch_taken _ _ _ = false -> _ =>
        solve [intros Hb _; exfalso; rewrite branch_eq_U, (U_atom _ 18 n V18 ltac:(lia)), U_lit in Hb by lia;
               apply Z.eqb_neq in Hb; lia] end
    | lazymatch goal with |- branch_taken _ _ _ = true -> _ => idtac end ].
  intros _ HS4. clear HS3.
  fsw_aj_runU pn_tbl_ok HS4 HJ2 HARU2.
  { pn_awr_ret E2b. apply awr_ok_nil. }
  lazymatch type of HS4 with st_ok _ _ _ (restrict _ ?m) => rename m into msM end.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W2) E2 _ msM HS4 eq_refl). cbn [ss_pc]. change 336316 with PC_memset.
  eapply SRr_mono;
    first
    [ lazymatch goal with |- SRr _ _ _ _ =>
        eapply (pn_tail ly S U W regs mem md n c db live peak cnt fail res ly2 S2 W2 (ms_regs msM) (ms_mem msM) _
          Hra FH HG Hc Hn Hlen Hdb HARU0 HJ2 HARU2 Hbl2);
        first
        [ lazymatch goal with |- getr _ _ = Z_to_bv 64 RA_PN_MEMSET =>
            solve [exact (fsw_reg_lit _ E2 _ msM 1%bv RA_PN_MEMSET HS4 ltac:(clear; vm_compute; reflexivity)
                            ltac:(clear; unfold RA_PN_MEMSET; lia))] end
        | lazymatch goal with |- spZ _ = _ => solve [unfold spZ at 1; pn_sr HS4 (2%bv : bv 5); rewrite fsw_SOff0; exact E2b] end
        | lazymatch goal with |- getr _ ?q = w64 (as_gp B) =>
            solve [pn_sr HS4 q; rewrite fsw_SOff0, (VQ 3%nat ltac:(lia)); exact Hgp] end
        | lazymatch goal with |- getr _ ?q = w64 (as_tp B) =>
            solve [pn_sr HS4 q; rewrite fsw_SOff0, (VQ 4%nat ltac:(lia)); exact Htp] end
        | lazymatch goal with |- getr _ ?q = w64 _ => solve [pn_val HS4 q E2] end
        | lazymatch goal with |- pn_frame _ _ _ _ =>
            solve [pose proof (fsw_region_nth E2 _ _ 0 _ HS4 eq_refl) as HR; cbn [ms_mem restrict] in HR;
                   exact (pn_frame_of_cs E2 _ _ _ regs EX2 E2b HR)] end
        | lazymatch goal with |- forall _, _ -> aview _ _ _ _ = _ => solve [intros i Hi; lia] end
        | lazymatch goal with |- forall _, _ -> getr _ _ = getr _ _ => solve [pn_rcsv HS4 VQ] end ] end
    | lazymatch goal with |- forall _, _ => idtac end ].
  intros W' c' _ (res0 & Hp). exists res0. exact Hp.
- destruct (HBLK ltac:(lia)) as (b & m & Hbm & Hbd & Hdn).
  eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 18 0) (b := SLit 0);
    first
    [ solve [exact HS3]
    | lazymatch goal with |- branch_taken _ _ _ = true -> _ =>
        solve [intros Hb _; exfalso; rewrite branch_eq_U, (U_atom _ 18 n V18 ltac:(lia)), U_lit in Hb by lia;
               apply Z.eqb_eq in Hb; lia] end
    | lazymatch goal with |- branch_taken _ _ _ = false -> _ => idtac end ].
  intros _ HS4. clear HS3.
  fsw_aj_runU pn_tbl_ok HS4 HJ2 HARU2.
  { pn_awr_ret E2b. apply awr_ok_nil. }
  lazymatch type of HS4 with st_ok _ _ _ (restrict _ ?mm) => rename mm into msC end.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W2) E2 _ msC HS4 eq_refl). cbn [ss_pc]. change 335136 with PC_memcpy.
  rewrite Hlen in Hdra, Hdam, Hdc.
  eapply SRr_mono;
    first
    [ lazymatch goal with |- SRr _ _ _ _ =>
        eapply (pn_mid ly S U W regs mem md n c db live peak cnt fail res ly2 S2 W2 (ms_regs msC) (ms_mem msC) _ d b m
          Hra FH HG Hc ltac:(lia) Hlen Hdb HARU0 Hdra Hdam Hd4 ltac:(lia) Hbm Hbd Hdn Hsrc0 HJ2 HARU2 Hbl2);
        first
        [ lazymatch goal with |- getr _ _ = Z_to_bv 64 RA_PN_MEMCPY =>
            solve [exact (fsw_reg_lit _ E2 _ msC 1%bv RA_PN_MEMCPY HS4 ltac:(clear; vm_compute; reflexivity)
                            ltac:(clear; unfold RA_PN_MEMCPY; lia))] end
        | lazymatch goal with |- spZ _ = _ => solve [unfold spZ at 1; pn_sr HS4 (2%bv : bv 5); rewrite fsw_SOff0; exact E2b] end
        | lazymatch goal with |- getr _ ?q = w64 (as_gp B) =>
            solve [pn_sr HS4 q; rewrite fsw_SOff0, (VQ 3%nat ltac:(lia)); exact Hgp] end
        | lazymatch goal with |- getr _ ?q = w64 (as_tp B) =>
            solve [pn_sr HS4 q; rewrite fsw_SOff0, (VQ 4%nat ltac:(lia)); exact Htp] end
        | lazymatch goal with |- getr _ ?q = w64 _ => solve [pn_val HS4 q E2] end
        | lazymatch goal with |- pn_frame _ _ _ _ =>
            solve [pose proof (fsw_region_nth E2 _ _ 0 _ HS4 eq_refl) as HR; cbn [ms_mem restrict] in HR;
                   exact (pn_frame_of_cs E2 _ _ _ regs EX2 E2b HR)] end
        | lazymatch goal with |- forall _, _ -> getr _ _ = getr _ _ => solve [pn_rcsv HS4 VQ] end ] end
    | lazymatch goal with |- forall _, _ => idtac end ].
  intros W' c' _ Hp. exact Hp.
Qed.

End W.

Set Printing Implicit.
About past_nul_ok.
Unset Printing Implicit.
Print Assumptions past_nul_ok.
