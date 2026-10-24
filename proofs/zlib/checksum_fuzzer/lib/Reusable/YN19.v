(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YK11 YK0s YK0h YK0i YK14 YK1b YK1a YK15 YK0v YK02 YP0n YM06 YK1j YM00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH00 YH03 YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0h YO0w YO0s YO0x YO0z YO14 YO0v YO0q YO0u YO15 YO10 YO12 YO11 YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a YO0c YO0b YN01 YN03 YN02
YN2b YN2e YN0g YN0d YN0c YN25 YN0a YN0p
YN2j YN2h YN2n YN2m YN2d YN2i
YN2k YN0j YN0h YN0i YN1k YN2w YN1d YN31 YN0z
YN13 YN1m YN15 YN16 YN12 YN1n YN1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Local Open Scope mm_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Notation B := src0_msyms.
Ltac inlist := cbn; repeat (first [left; reflexivity | right]).
Ltac lits := unfold LOCK, CTX, LIBC, ERRNO, TP, GOT, GUARD, SCT, SCNT, MCNT, ASF, DEB, src0_D_malloc_lock, src0_D_malloc_context, src0_D_libc, src0_tp,
src0_D_got_stack_chk_guard, src0_D_stack_chk_guard, src0_D_size_classes, src0_D_small_cnt_tab, src0_D_med_cnt_tab, src0_D_debruijn32 in *.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma rom_tabs : forallb (fun i => match seg_rom src0segs (Z_to_bv 64 (DEB + i)) with Some _ => true | None => false end) (zseq 0 159) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma src0_tabs_img : forall x, DEB <= x < DEB + 159 -> in_img B x.
Proof. intros x Hx. eapply (covered_sound B 0x10000 0x3000); [vm_compute; reflexivity | unfold DEB, src0_D_debruijn32 in Hx; lia]. Qed.
Lemma tabs_region_ok : forall E m, statics_ok B m -> region_ok src0segs E m R_tabs.
Proof.
intros E m ST. unfold region_ok, R_tabs. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
split; [lits; lia|]. split; [lits; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [| apply Forall_nil]. intros i Hi. cbn [c_off c_val c_len cv_len] in Hi |- *.
pose proof rom_tabs as T. rewrite forallb_forall in T. specialize (T i (zseq_In 0 159 i ltac:(lia) ltac:(lia))).
rewrite Z.add_0_l. unfold cbyte, img_byte.
destruct (seg_rom src0segs (Z_to_bv 64 (DEB + i))) as [b|] eqn:Eb; [| discriminate]. exists b. split; [reflexivity|].
change src0segs with (ms_segs B). rewrite (st_tables _ _ ST); [exact Eb|]. unfold table_addr. cbn [ms_debruijn ms_size_classes ms_small_cnt ms_med_cnt src0_msyms]. lits. lia.
Qed.
Lemma regs_at_In : forall (f : reg -> sv) l1 l2 r v, map f l1 = l2 -> In (r, v) (combine l1 l2) -> f r = v.
Proof.
intros f l1. induction l1 as [|a t IHl]; intros l2 r v Hm Hi; [destruct l2; destruct Hi|].
destruct l2 as [|b l2]; [discriminate|]. cbn in Hm. injection Hm as Hb Ht. cbn in Hi.
destruct Hi as [E1|Hi]; [injection E1 as <- <-; exact Hb | exact (IHl l2 r v Ht Hi)].
Qed.
Section s.
Variables (X : list sptr) (U : Z -> Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (sc n stk : Z).
Hypothesis HI : Inv X None U A.
Hypothesis XR : rawX X A.
Hypothesis AMA : ama_ok A.
Hypothesis BND : bounded A.
Hypothesis RSV : rsv_ok A.
Hypothesis SPOK : span_ok A.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hn : 0 <= n < MMAP_THRESHOLD.
Hypothesis MID : midrep B L A mem md.
Hypothesis AUXP : st_init_done A = false -> auxv_pre B (ly_sec L) (spZ regs) mem.
Hypothesis PRE : callee_pre B regs mem stk.
Hypothesis Hstk : ASF <= stk <= AS_STACK.
Hypothesis R10 : getr regs 10 = Z_to_bv 64 sc.
Hypothesis R11 : getr regs 11 = Z_to_bv 64 n.
Hypothesis AMH : alloc_meta_hyp B.
Variable g : Z.
Hypothesis Hg : word_mem src0segs mem GUARD g.
Variables (j1 j2 : Z).
Hypothesis HU : forall k, U k = 0.
Hypothesis HB : as_budget sc <= stk.
Variable fuel : nat.
Hypothesis HN : (need sc <= S (S fuel))%nat.
Hypothesis IH : ASH fuel.
Let sp : Z := bv_unsigned (getr regs 2).
Local Notation csn := (cs L A sc g j1 j2).
Local Notation E00 := (E0 regs csn).
Local Notation WSn := (WS regs).
Let agree_cs' := agree_cs L A regs sc g j1 j2.
Let sv_cs' := sv_cs L A regs sc g j1 j2.
Let agree_reg' := agree_reg L A regs sc g j1 j2.
Let cs_facts' := cs_facts X U L A regs mem md sc HI Hsc MID g j1 j2.
Let pre_facts' := pre_facts regs mem stk PRE.
Let nu : Z := cs L A sc g j1 j2 35.
Local Notation POSTn := (POST X L A regs mem md sc stk g).
Lemma key_factsR : forall X' R' L1 A1 mm md1 q, Inv X' R' U A1 -> midrep B L1 A1 mm md1 -> In q (keys A1) ->
(forall x, ptr_addr L1 q <= x < ptr_addr L1 q + META_SIZE -> present mm x /\ ~ in_img B x /\ 4096 <= x < alloc_ceiling) /\
ptr_addr L1 q mod 8 = 0 /\
(forall c, In c (meta_slot_cells q (MT A1 q)) -> In c (image A1)) /\
(exists a k, In a (st_areas A1) /\ 0 <= k < METAS_PER_AREA /\ q = slot_of a k) /\
(prid q < length (st_regions A1))%nat.
Proof.
intros X' R' L1 A1 mm md1 q HIq HM Hq.
pose proof (inv_keys HIq) as (_ & KP & _ & _ & Kc). destruct (KP q Hq) as (a & k & Ha & Hk & Eq).
assert (Hk' : 0 <= k < METAS_PER_AREA) by (unfold handed in Hk; destruct (sptr_eqb a _); lia).
assert (PG : forall x, ptr_addr L1 q <= x < ptr_addr L1 q + META_SIZE -> ptr_addr L1 a <= x < ptr_addr L1 a + PGSZ).
{ intros x Hx. rewrite Eq, ptr_addr_padd in Hx. unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. lia. }
pose proof (inv_areas HIq) as (_ & Hareas & _). destruct (Hareas a Ha) as (r & o & rg & Ear & Ho & Hlo & Hr & Hl & _).
split; [| split; [| split; [| split]]].
- intros x Hx. specialize (PG x Hx). pose proof (areas_off_img B X' R' U L1 A1 mm md1 HIq HM a x Ha PG) as [NI Rx].
split; [| split; [exact NI | exact Rx]].
pose proof (mid_mem _ _ _ _ _ HM) as (_ & _ & FT).
assert (Hin : In (LMem a, PGSZ) (footprint A1)) by (right; apply in_app_iff; left; apply in_map_iff; eexists; split; [reflexivity | exact Ha]).
pose proof (proj1 (Forall_forall _ _) FT _ Hin) as FO. cbn [foot_ok fst snd] in FO. apply FO. exact PG.
- pose proof (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ HM) r rg Hr Hl) as (Hal & _).
rewrite Eq, ptr_addr_padd, Ear. unfold ptr_addr. cbn [loc_addr]. unfold PGSZ in Hal, Ho. unfold AREA_HDR, META_SIZE.
pose proof (proj2 (Z.div_exact (ly_reg L1 r) 4096 ltac:(lia)) Hal) as Hb. pose proof (proj2 (Z.div_exact o 4096 ltac:(lia)) Ho) as Hob.
replace (ly_reg L1 r + o + (24 + 40 * k)) with ((512 * (ly_reg L1 r / 4096) + 512 * (o / 4096) + 3 + 5 * k) * 8) by lia. apply Z_mod_mult.
- intros c Hc. unfold image. rewrite !in_app_iff. right. left. apply (slot_cells_in_areas A1 (st_areas A1) a k c Ha Hk'). unfold slot_of. rewrite <- Eq. exact Hc.
- exists a, k. split; [exact Ha|]. split; [exact Hk'|]. exact Eq.
- rewrite Eq. unfold slot_of. rewrite prid_padd, Ear. cbn [prid]. exact (region_of_lt _ _ _ Hr).
Qed.
Lemma mslot_zeroR : forall X' R' L1 A1 mm md1 q, Inv X' R' U A1 -> midrep B L1 A1 mm md1 -> In q (keys A1) -> rawm A1 q ->
forall i, 0 <= i < 40 -> mbyte src0segs mm (ptr_addr L1 q + i) = Some (Z_to_bv 8 0).
Proof.
intros X' R' L1 A1 mm md1 q HIq HM Hq Mq. destruct (key_factsR X' R' L1 A1 mm md1 q HIq HM Hq) as (_ & _ & CELLS & _).
pose proof (memrep_cell B L1 A1 mm) as MC.
assert (BY : forall off w, In (MCell (LMem (padd q off)) w (VZ 0)) (meta_slot_cells q (MT A1 q)) -> forall jj, (jj < w)%nat -> mbyte src0segs mm (ptr_addr L1 q + off + Z.of_nat jj) = Some (Z_to_bv 8 0)).
{ intros off w Hin jj Hj. pose proof (MC _ (mid_mem _ _ _ _ _ HM) (CELLS _ Hin)) as C. unfold cell_mem in C. cbn [mc_loc mc_w mc_val sval_num] in C.
change (loc_addr L1 (LMem (padd q off))) with (ptr_addr L1 (padd q off)) in C. rewrite ptr_addr_padd in C. change (ms_segs B) with src0segs in C.
rewrite (C jj Hj). f_equal. f_equal. unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity. }
assert (IN : forall off w, In (MCell (LMem (padd q off)) w (VZ 0)) [MCell (LMem (padd q META_prev)) 8 (VZ 0); MCell (LMem (padd q META_next)) 8 (VZ 0); MCell (LMem (padd q META_mem)) 8 (VZ 0);
MCell (LMem (padd q META_avail)) 4 (VZ 0); MCell (LMem (padd q META_freed)) 4 (VZ 0); MCell (LMem (padd q META_bits)) 8 (VZ 0)] ->
In (MCell (LMem (padd q off)) w (VZ 0)) (meta_slot_cells q (MT A1 q))).
{ intros off w Hin. destruct Mq as [E1|E1]; rewrite E1; cbn [meta_slot_cells optr]; exact Hin. }
intros i Hi.
assert (CASES : exists off w jj, (In (off, w) [(0, 8%nat); (8, 8%nat); (16, 8%nat); (24, 4%nat); (28, 4%nat); (32, 8%nat)]) /\ (jj < w)%nat /\ i = off + Z.of_nat jj).
{ destruct (Z_lt_le_dec i 8); [exists 0, 8%nat, (Z.to_nat i); split; [inlist | split; lia]|].
destruct (Z_lt_le_dec i 16); [exists 8, 8%nat, (Z.to_nat (i - 8)); split; [inlist | split; lia]|].
destruct (Z_lt_le_dec i 24); [exists 16, 8%nat, (Z.to_nat (i - 16)); split; [inlist | split; lia]|].
destruct (Z_lt_le_dec i 28); [exists 24, 4%nat, (Z.to_nat (i - 24)); split; [inlist | split; lia]|].
destruct (Z_lt_le_dec i 32); [exists 28, 4%nat, (Z.to_nat (i - 28)); split; [inlist | split; lia]|].
exists 32, 8%nat, (Z.to_nat (i - 32)); split; [inlist | split; lia]. }
destruct CASES as (off & w & jj & Hin & Hj & ->). rewrite Z.add_assoc. apply (BY off w); [| exact Hj].
apply IN. unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits. cbn [In] in Hin.
destruct Hin as [H|[H|[H|[H|[H|[H|[]]]]]]]; injection H as <- <-; inlist.
Qed.
Lemma owned_low_mid : forall X' R' L1 A1 mm md1 x, Inv X' R' U A1 -> midrep B L1 A1 mm md1 -> owned B L1 A1 x -> 0 <= x < alloc_ceiling.
Proof.
intros X' R' L1 A1 mm md1 x HIq HM [[(rg & Hrg & Hx) _] | Hs].
- pose proof (mid_syms _ _ _ _ _ HM) as SO.
destruct (In_footprint_inv A1 rg Hrg) as [-> | [(a & Ha & ->) | (k & r & Hr & Hk & Hl & ->)]]; cbn [fst snd loc_addr] in Hx.
+ rewrite (mid_ctx _ _ _ _ _ HM) in Hx. pose proof (so_ctx_lo _ SO). pose proof (so_ctx_hi _ SO). lia.
+ destruct (inv_areas HIq) as (_ & Hareas & _).
destruct (Hareas a Ha) as (r & o & rg & -> & _ & Ho & Hr & Hl & Hlen & _). cbn [loc_addr] in Hx.
destruct (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ HM) r rg Hr Hl) as (_ & H1 & H2 & _). unfold PGSZ in *. lia.
+ destruct (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ HM) k r Hr Hl) as (_ & H1 & H2 & _). lia.
- pose proof (mid_syms _ _ _ _ _ HM) as SO. apply (so_img_hi _ SO). apply (so_statics_img _ SO). exact Hs.
Qed.
Lemma ctx_word_mid : forall L1 A1 mm md1 off v, midrep B L1 A1 mm md1 -> In (MCell (LCtx off) 8 v) (ctx_cells A1) -> (forall z, v <> VLo5 z) ->
word_mem src0segs mm (CTX + off) (sval_num L1 v).
Proof.
intros L1 A1 mm md1 off v HM Hin Hv. pose proof (memrep_cell B L1 A1 mm _ (mid_mem _ _ _ _ _ HM) ltac:(unfold image; apply in_app_iff; left; exact Hin)) as C.
unfold cell_mem in C. cbn [mc_loc mc_w mc_val loc_addr] in C. rewrite (mid_ctx _ _ _ _ _ HM) in C. change (ms_ctx B) with CTX in C.
destruct v as [z|p|z|]; try exact C. exfalso. exact (Hv z eq_refl).
Qed.
Lemma active_word_mid : forall X' R' L1 A1 mm md1 c, Inv X' R' U A1 -> midrep B L1 A1 mm md1 -> 0 <= c < 48 ->
word_mem src0segs mm (LOCK + 88 + 8 * c) (onum L1 (active_hd A1 c)).
Proof.
intros X' R' L1 A1 mm md1 c HIq HM Hc.
replace (LOCK + 88 + 8 * c) with (CTX + (CTX_active + 8 * Z.of_nat (Z.to_nat c))) by (unfold LOCK, CTX, CTX_active, src0_D_malloc_lock, src0_D_malloc_context; lia).
replace (onum L1 (active_hd A1 c)) with (sval_num L1 (optr (active_hd A1 c))) by (destruct (active_hd A1 c); reflexivity).
apply (ctx_word_mid L1 A1 mm md1); [exact HM | | destruct (active_hd A1 c); intros z; discriminate].
unfold ctx_cells. apply in_app_iff. right. apply in_app_iff. left. apply in_map_iff. exists (Z.to_nat c). split; [unfold active_hd; reflexivity | apply in_seq; lia].
Qed.
Lemma ctr_bytes_mid : forall L1 A1 mm md1, midrep B L1 A1 mm md1 ->
forall kk, (kk < 4)%nat -> mbyte src0segs mm (LOCK + 20 + Z.of_nat kk) = Some (Z_to_bv 8 (le_byte (st_mmap_counter A1) 4 kk)).
Proof.
intros L1 A1 mm md1 HM kk Hk.
pose proof (memrep_cell B L1 A1 mm (MCell (LCtx CTX_mmap_counter) 4 (VZ (st_mmap_counter A1))) (mid_mem _ _ _ _ _ HM) ltac:(unfold image; apply in_app_iff; left; unfold ctx_cells; cbn [In]; right; right; left; reflexivity)) as C.
unfold cell_mem in C. cbn [mc_loc mc_w mc_val loc_addr sval_num] in C. rewrite (mid_ctx _ _ _ _ _ HM) in C. change (ms_ctx B) with CTX in C. change (ms_segs B) with src0segs in C.
replace (LOCK + 20) with (CTX + CTX_mmap_counter) by (unfold CTX_mmap_counter; lits; lia). exact (C kk Hk).
Qed.
Lemma ptr_addr_le : forall sA LA LB p, layout_le sA LA LB -> (prid p < length (st_regions sA))%nat -> ptr_addr LB p = ptr_addr LA p.
Proof. intros sA LA LB p (_ & _ & _ & Y4) Hp. unfold ptr_addr. rewrite !loc_addr_LMem, (Y4 (prid p) Hp). reflexivity. Qed.
Lemma user_blocks_keep : forall XA XB RB sA sB LA LB, Inv XA None U sA -> Xclean XA sA -> Inv XB RB U sB -> ub_same sA sB -> layout_le sA LA LB ->
forall x, in_user_block LB sB x <-> in_user_block LA sA x.
Proof.
intros XA XB RB sA sB LA LB HIA XCA HIB UB LE x.
pose proof (ub_same_user_blocks sA sB (proj1 (inv_keys HIA)) (proj1 (inv_keys HIB)) UB) as EUB.
assert (ADDR : forall b, In b (user_blocks sA) -> loc_addr LB (LMem (fst b)) = loc_addr LA (LMem (fst b))).
{ intros b Hb. destruct (in_user_blocks_inv sA b Hb) as (g' & am & i & fr & Hg' & Hi & Hfr & Hk & ->). cbn [fst].
apply (used_metas_usedX' XA None U sA HIA XCA) in Hg'.
destruct (used_group_region XA None U sA g' am HIA Hg') as (rg & Hr & _).
change (loc_addr LB (LMem (frame_ptr am i fr))) with (ptr_addr LB (frame_ptr am i fr)). change (loc_addr LA (LMem (frame_ptr am i fr))) with (ptr_addr LA (frame_ptr am i fr)).
apply (ptr_addr_le sA LA LB _ LE). unfold frame_ptr, slot_start. rewrite !prid_padd. exact (region_of_lt _ _ _ Hr). }
unfold in_user_block. rewrite EUB. split; intros (b & Hb & Hx); exists b; split; [exact Hb | rewrite <- (ADDR b Hb); exact Hx | exact Hb | rewrite (ADDR b Hb); exact Hx].
Qed.
Lemma owned_mono : forall XA XB RB sA sB LA LB x, Inv XA None U sA -> Xclean XA sA -> Inv XB RB U sB -> as_keep XA sA sB -> ub_same sA sB -> layout_le sA LA LB ->
owned B LA sA x -> owned B LB sB x.
Proof.
intros XA XB RB sA sB LA LB x HIA XCA HIB (_ & KA & KR) UB LE Ho. destruct Ho as [[(rg & Hrg & Hx) NB] | Hs]; [| right; exact Hs].
left. split; [| intros Hb; apply NB; exact (proj1 (user_blocks_keep XA XB RB sA sB LA LB HIA XCA HIB UB LE x) Hb)].
pose proof LE as (Yc & _ & _ & Y4).
destruct (In_footprint_inv sA rg Hrg) as [-> | [(a & Ha & ->) | (k & r & Hr & Hk & Hl & ->)]]; cbn [fst snd] in Hx.
- exists (LCtx 0, CTX_SIZE). split; [left; reflexivity|]. cbn [fst snd loc_addr] in *. rewrite Yc. exact Hx.
- exists (LMem a, PGSZ). split; [right; apply in_app_iff; left; apply in_map_iff; exists a; split; [reflexivity | exact (KA a Ha)]|]. cbn [fst snd].
change (loc_addr LB (LMem a)) with (ptr_addr LB a). change (loc_addr LA (LMem a)) with (ptr_addr LA a) in Hx.
rewrite (ptr_addr_le sA LA LB a LE); [exact Hx|]. exact (area_prid XA None U sA HIA a Ha).
- destruct (KR k r Hr Hl) as (r' & Hr' & Hl' & Hk' & Hlen). exists (LMem (SP k 0), rg_len r'). split; [apply footprint_region_In; [exact Hr' | tauto | exact Hl']|].
cbn [fst snd loc_addr] in *. rewrite (Y4 k (region_of_lt _ _ _ Hr)). lia.
Qed.
Lemma nonmap_keep : forall XA XB RB sA sB LA LB x, Inv XA None U sA -> Xclean XA sA -> Inv XB RB U sB -> as_keep XA sA sB -> ub_same sA sB -> layout_le sA LA LB ->
in_nonmap_region LA sA x -> ~ owned B LB sB x -> in_nonmap_region LB sB x.
Proof.
intros XA XB RB sA sB LA LB x HIA XCA HIB (_ & KA & KR) UB LE [(r & rg & Hr & Hl & Hk & Hx) NM] NO. pose proof LE as (Yc & _ & _ & Y4).
split.
- destruct (KR r rg Hr Hl) as (rg' & Hr' & Hl' & Hk' & Hlen). exists r, rg'. split; [exact Hr'|]. split; [exact Hl'|]. split; [intros E; apply Hk; tauto|].
rewrite (Y4 r (region_of_lt _ _ _ Hr)). lia.
- intros (k & rg2 & Hk2 & Hl2 & Hkd2 & Hx2). apply NO. left. split.
+ exists (LMem (SP k 0), rg_len rg2). split; [apply footprint_region_In; assumption|]. cbn [fst snd loc_addr]. lia.
+ intros Hb. apply (proj1 (user_blocks_keep XA XB RB sA sB LA LB HIA XCA HIB UB LE x)) in Hb. destruct Hb as ([bp bn] & Hb & Hbx). cbn [fst snd] in Hbx.
destruct (user_block_in_map XA U sA LA bp bn x HIA XCA Hb Hbx) as (k0 & rg0 & Hk0 & Hkd0 & Hl0 & Hx0).
apply NM. exists k0, rg0. split; [exact Hk0|]. split; [exact Hl0|]. split; [exact Hkd0 | exact Hx0].
Qed.
Section NA.
Variables (m : sptr) (s1 : astate) (L1 : layout) (mem1 : word -> option byte) (md1 : Model).
Hypothesis HI1 : Inv (m :: X) None U s1.
Hypothesis RX1 : rawX X s1.
Hypothesis AK1 : as_keep X A s1.
Hypothesis Mm : MT s1 m = Some MRaw \/ MT s1 m = Some (MFree None None).
Hypothesis Km : In m (keys s1).
Hypothesis NXm : memb m X = false.
Hypothesis US1 : forall g' am, usedX (m :: X) s1 g' am <-> usedX X A g' am.
Hypothesis ACT1 : st_active s1 = st_active A.
Hypothesis LEN1 : (length (st_regions A) <= length (st_regions s1))%nat.
Hypothesis LE1 : layout_le A L L1.
Hypothesis MID1 : midrep B L1 s1 mem1 md1.
Hypothesis AMA1 : ama_ok s1.
Hypothesis BND1 : bounded s1.
Hypothesis VM1 : exists vm', md1 = with_vmmaps vm' md.
Hypothesis FR1 : forall x, 0 <= x < 2 ^ 64 -> ~ WSn x -> ~ (ERRNO <= x < ERRNO + 4) -> ~ (CTX <= x < CTX + CTX_SIZE) -> ~ in_nonmap_region L1 s1 x ->
mem1 (Z_to_bv 64 x) = mem (Z_to_bv 64 x).
Hypothesis ERRW1 : forall a, ERRNO <= a < ERRNO + 4 -> writable_at src0segs mem1 a.
Variable E : env.
Hypothesis HA : env_agree 40 E00 E.
Hypothesis E40 : ew E 40 = Z_to_bv 64 (ptr_addr L1 m).
Hypothesis E56 : ew E 56 = Z_to_bv 64 (usage_of s1 sc).
Hypothesis E61 : ew E 61 = Z_to_bv 64 (initial_cnt sc (usage_of s1 sc)).
Hypothesis E62 : ew E 62 = Z_to_bv 64 (16 * nu * initial_cnt sc (usage_of s1 sc)).
Let K : Z := initial_cnt sc (usage_of s1 sc).
Let k : Z := nu * K.
Let total : Z := 16 * k + 12.
Let j : Z := jof k.
Hypothesis ARM : class_size sc * K + UNIT <= PGSZ / 2.
Let Mh1 : m_halted md1 = None := proj1 (mid_md _ _ _ _ _ MID1).
Let Mlz1 : m_vm_lazy md1 = [] := proj1 (proj2 (mid_md _ _ _ _ _ MID1)).
Local Notation FRM1n := (FRM1 regs mem1).
Lemma XC1n : Xclean (m :: X) s1.
Proof.
intros x am [<-|Hx] Hu; [destruct Mm as [Mq|Mq]; rewrite Mq in Hu; discriminate|]. destruct (RX1 x Hx) as [Mq|Mq]; rewrite Mq in Hu; discriminate.
Qed.
Lemma facts_N : In k KSET /\ size_to_class total = j /\ (j = 15 \/ j = 19 \/ j = 23) /\ class_size j = csz j /\ total + IB <= class_size j /\
28 <= k <= 126 /\ total = UNIT + K * class_size sc - IB /\ sc <= 23 /\ sc < j /\ (need j + 2 <= need sc)%nat /\ 0 <= j < 48 /\ 2 <= K <= 32 /\ 1 <= nu.
Proof.
pose proof (nu_facts X U L A regs mem md sc HI Hsc MID g j1 j2) as [N1 N2]. fold nu in N1, N2.
pose proof (initial_cnt_facts sc (usage_of s1 sc) Hsc) as (K1 & K2 & K26). fold K in K1, K2, K26.
assert (Enu : znth sc size_classes = nu) by (unfold class_size, UNIT in N2; lia).
pose proof (nested_k sc (usage_of s1 sc) Hsc ARM) as HK. fold K in HK. rewrite Enu in HK. fold k in HK.
destruct (kset_facts k HK) as (J1 & J2 & J3 & J4 & J5). unfold YN1b.jof in J1, J2, J3, J4. fold (jof k) in J1, J2, J3, J4. fold j in J1, J2, J3, J4.
assert (Etot : total = UNIT + K * class_size sc - IB) by (subst total k; rewrite N2; unfold UNIT, IB; lia).
pose proof (nested_facts sc K Hsc ltac:(lia) K26 ARM) as NF. cbv zeta in NF. rewrite <- Etot in NF.
replace (size_to_class total) with j in NF by (symmetry; exact J1).
destruct NF as (H23 & HK2 & Htot & Hscj & Hj48 & Hfit & Hlt).
pose proof (need_nested sc j H23 ltac:(lia)) as NN.
assert (J3' : class_size j = csz j).
{ rewrite J3. unfold csz. destruct J2 as [Ej|[Ej|Ej]]; rewrite Ej in *; subst j; unfold YN1b.jof in Ej;
destruct (k <? 32); destruct (k <? 64); cbn; lia. }
split; [exact HK|]. split; [exact J1|]. split; [exact J2|]. split; [exact J3'|]. split; [exact Hfit|]. split; [exact J5|]. split; [exact Etot|].
split; [exact H23|]. split; [lia|]. split; [exact NN|]. split; [exact Hj48|]. split; [lia | lia].
Qed.
Definition callst : sstate := mkSS src0_A_alloc_slot (ss_regs (ss_NC j)) (ss_mem (ss_NC j)) None (ss_facts (ssN1 k)).
Lemma statics1 : forall mm, FRM1n mm -> statics_ok B mm.
Proof.
intros mm HF. pose proof pre_facts' as (_ & _ & P3 & _). pose proof (mid_syms _ _ _ _ _ MID1) as SO.
apply (YN2d.statics_ok_ext B s1 0 mem1); [| exact (mid_statics _ _ _ _ _ MID1)].
intros x Hx. pose proof (proj1 alloc_ceiling_val) as AC. pose proof (so_img_hi _ SO x (so_statics_img _ SO x Hx)) as Hhi. apply HF; [lia|]. unfold WS, ASF in *. lia.
Qed.
Lemma to_N1 : forall ms, st_ok src0segs E (add_cond ss_g4 C_nest) ms -> FRM1n (ms_mem ms) -> st_ok src0segs E (ssN1 k) ms.
Proof.
intros ms HS HF. pose proof facts_N as (HK & _ & _ & _ & _ & Hk & _ & _ & _ & _ & _ & HKr & Hnu).
destruct cs_facts' as (C33 & _). pose proof pre_facts' as (_ & _ & P3 & P4 & _). pose proof (proj1 alloc_ceiling_val) as AC.
assert (E33 : bv_unsigned (ew E 33) = cs L A sc g j1 j2 33) by (rewrite (agree_cs' E 33 HA) by lia; apply u64_of_Z; lits; lia).
assert (E2 : bv_unsigned (ew E 2) = sp) by (rewrite (agree_reg' E 2 HA) by lia; reflexivity).
assert (U62 : bv_unsigned (ew E 62) = 16 * k) by (rewrite E62; subst k; rewrite u64_of_Z by nia; lia).
unfold ssN1. apply st_ok_add_alias.
- apply (st_ok_add_fact src0segs E (mkSS (ss_pc (add_cond ss_g4 C_nest)) (ss_regs (add_cond ss_g4 C_nest)) (R_tabs :: ss_mem (add_cond ss_g4 C_nest)) None (ss_facts (add_cond ss_g4 C_nest)))).
+ apply (st_ok_add_region src0segs E (add_cond ss_g4 C_nest) ms R_tabs HS); [vm_compute; reflexivity | apply tabs_region_ok; apply statics1; exact HF |].
change (ss_mem (add_cond ss_g4 C_nest)) with (ss_mem ss_g4).
assert (SK : map (fun r => (r_base r, r_lo r, r_hi r)) (ss_mem ss_g4) = [(Some 33%nat, 472, 480); (Some 2%nat, -ASF, 0); (None, GOT, GOT + 8); (None, GUARD, GUARD + 8); (None, LIBC + 48, LIBC + 56)]) by (vm_compute; reflexivity).
destruct (ss_mem ss_g4) as [|r1 [|r2 [|r3 [|r4 [|r5 [|r6 l]]]]]]; try discriminate SK. injection SK as B1 L1' H1 B2 L2 H2 B3 L3 H3 B4 L4 H4 B5 L5 H5.
repeat apply Forall_cons; try apply Forall_nil; unfold extent_disjoint; cbn [r_base r_lo r_hi R_tabs base_val]; rewrite ?B1, ?L1', ?H1, ?B2, ?L2, ?H2, ?B3, ?L3, ?H3, ?B4, ?L4, ?H4, ?B5, ?L5, ?H5; cbn [base_val]; rewrite ?E33, ?E2; cbn [cs]; lits; unfold ASF in *; lia.
+ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U62. split; [lia|]. split; [| lia]. change (2 ^ 4) with 16. rewrite Z.mul_comm, Z_mod_mult. reflexivity.
- apply U_inj. rewrite U_SAlu, U_SOff, !U_SLit. cbn [zalu_raw]. rewrite U62, Z.add_0_r. unfold zcanon, M64.
rewrite (Z.mod_small (16 * k)), (Z.mod_small 4) by lia. change (Z.land 4 63) with 4. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
replace (16 * k / 16) with k by (rewrite Z.mul_comm, Z_div_mult by lia; reflexivity). reflexivity.
Qed.
Definition NCpost (c : config) : Prop := exists ms, c = mkCfg ms md1 /\ st_ok src0segs E callst ms /\ FRM1n (ms_mem ms).
Lemma wsub_N1 : wsub (R_tabs :: ss_mem ss_g4) SKS = true. Proof. vm_compute. reflexivity. Qed.
Lemma reach_NC : forall ms, st_ok src0segs E (add_cond ss_g4 C_nest) ms -> FRM1n (ms_mem ms) -> SR src0segs (mkCfg ms md1) NCpost.
Proof.
intros ms HS HF. pose proof facts_N as (HK & _).
pose proof (to_N1 ms HS HF) as HS1.
eapply (SR_run_to_gen src0segs src0tbl src0tbl_ok FUEL src0_A_alloc_slot E (ssN1 k) _ RS_running); [exact Mh1 | exact Mlz1 | exact HS1 | exact (run_N1 k HK) |].
intros ms' HS' Hfr. apply SR_ret. exists ms'. split; [reflexivity|]. split; [exact HS'|].
apply (FRM1_run L A regs sc g j1 j2 s1 mem1 E (ss_mem (ssN1 k)) (ms_mem ms) (ms_mem ms') HA HF Hfr). exact wsub_N1.
Qed.
Lemma init1 : st_init_done s1 = true.
Proof.
destruct (st_init_done s1) eqn:Ei; [reflexivity|]. exfalso.
pose proof (inv_ctx HI1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Cinit). destruct (Cinit Ei) as (Em & _).
unfold keys in Km. rewrite Em in Km. exact Km.
Qed.
Lemma rawX1 : rawX (m :: X) s1.
Proof. intros x [<-|Hx]; [exact Mm | exact (RX1 x Hx)]. Qed.
Lemma call_facts : forall ms, st_ok src0segs E callst ms -> FRM1n (ms_mem ms) ->
ms = mkst (ms_regs ms) (Z_to_bv 64 src0_A_alloc_slot) (ms_mem ms) (seg_rom src0segs) /\
getr (ms_regs ms) 1 = Z_to_bv 64 PS_RAS /\ spZ (ms_regs ms) = sp - 144 /\ getr (ms_regs ms) 2 = Z_to_bv 64 (sp - 144) /\
getr (ms_regs ms) 10 = Z_to_bv 64 j /\ getr (ms_regs ms) 11 = Z_to_bv 64 total /\
callee_pre B (ms_regs ms) (ms_mem ms) (stk - 144) /\ midrep B L1 s1 (ms_mem ms) md1 /\ word_mem src0segs (ms_mem ms) GUARD g /\
(st_init_done s1 = false -> auxv_pre B (ly_sec L1) (spZ (ms_regs ms)) (ms_mem ms)) /\
regs_ok E (ss_regs (ss_NC j)) (ms_regs ms) /\
region_ok src0segs E (ms_mem ms) R_frame /\
(forall a, sp - ASF <= a < sp -> writable_at src0segs (ms_mem ms) a).
Proof.
intros ms HS HF. set (regs1 := ms_regs ms). set (mem' := ms_mem ms). pose proof facts_N as (HK & Hj & J3 & Hcs & Hfit & Hk & Etot & H23 & Hscj & NN & Hj48 & HKr & Hnu).
pose proof pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7). pose proof (proj1 alloc_ceiling_val) as AC. destruct cs_facts' as (C33 & _).
destruct (NC_regs j J3) as (RG & MEMj & PCj).
assert (Ems : ms = mkst regs1 (Z_to_bv 64 src0_A_alloc_slot) mem' (seg_rom src0segs)) by (exact (st_ok_mkst E callst ms HS eq_refl)).
pose proof HS as (S1 & S2 & S3 & S4 & S5 & S6 & Hregs & Hmem & HG).
assert (RD : forall r v, In (r, v) (combine [1; 2; 4; 10; 11; 18; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv
[SLit PS_RAS; SOff 2 (-144); SLit TP; SLit j; SOff 62 12; SLit j; SOff 10 0; SOff 40 0; SOff 61 0; SLit GUARD; SOff 33 88; SLit LOCK; SOff 33 0; SAlu ALU_SLL (SOff 35 0) (SLit 4); SLit SCT; SOff 26 0; SOff 27 0]) ->
getr regs1 r = sv_denot E v).
{ intros r v Hin. unfold regs_at in RG. rewrite <- (regs_at_In _ _ _ r v RG Hin). apply Hregs. }
assert (E2 : ew E 2 = getr regs 2) by (apply (agree_reg' E 2 HA); lia).
assert (R2 : getr regs1 2 = Z_to_bv 64 (sp - 144)).
{ rewrite (RD 2%bv (SOff 2 (-144))) by inlist. cbn [sv_denot]. rewrite E2. fold sp. apply f_equal. lia. }
assert (SPZ : spZ regs1 = sp - 144) by (unfold spZ; rewrite R2; apply u64_of_Z; unfold ASF in Hstk; lia).
assert (MIDc : midrep B L1 s1 mem' md1).
{ apply (midrep_stack_gen U regs mem stk PRE Hstk (m :: X) L1 s1 mem1 md1 mem' HI1 XC1n AMA1 MID1). exact HF. }
assert (RSTK : nth_error (ss_mem callst) 2 = Some R_frame) by (unfold callst; cbn [ss_mem]; rewrite MEMj; vm_compute; reflexivity).
pose proof (YN0d.st_ok_region src0segs E callst ms 2 _ HS RSTK) as RF. fold mem' in RF.
pose proof RF as (_ & _ & WSTK & CSTK). cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_frame] in WSTK. rewrite E2 in WSTK. fold sp in WSTK.
assert (WST : forall a, sp - ASF <= a < sp -> writable_at src0segs mem' a).
{ intros a Ha. replace a with (sp + (a - sp)) by lia. apply WSTK. lia. }
assert (GD : word_mem src0segs mem' GUARD g).
{ assert (RGD : nth_error (ss_mem callst) 4 = Some R_guard) by (unfold callst; cbn [ss_mem]; rewrite MEMj; vm_compute; reflexivity).
exact (guard_of_state L A regs sc g j1 j2 E callst ms 4 HS HA RGD). }
split; [exact Ems|]. split; [rewrite (RD 1%bv (SLit PS_RAS)) by inlist; reflexivity|]. split; [exact SPZ|]. split; [exact R2|].
split; [rewrite (RD 10%bv (SLit j)) by inlist; cbn [sv_denot]; reflexivity|].
split.
{ rewrite (RD 11%bv (SOff 62 12)) by inlist. cbn [sv_denot]. rewrite E62. fold K.
rewrite (u64_of_Z (16 * nu * K)) by nia. apply f_equal. unfold total, k. lia. }
split.
{ unfold callee_pre. rewrite SPZ. change (errno_addr B) with ERRNO. change (ms_tp B) with TP. rewrite ?B_segs.
split; [rewrite (RD 1%bv (SLit PS_RAS)) by inlist; cbn [sv_denot]; vm_compute; reflexivity|].
split; [unfold sp; rewrite <- Zminus_mod_idemp_l; unfold sp in P2; rewrite P2; reflexivity|].
split; [unfold ASF in Hstk; lia|]. split; [lia|].
split.
{ intros a Ha. destruct (Z_lt_le_dec a (sp - ASF)) as [Hlo|Hhi].
- apply (writable_ext1 mem); [| apply P5; lia]. subst mem'. rewrite (HF a) by (first [lia | unfold WS; lia]).
apply FR1; [lia | unfold WS; lia | lits; lia | unfold CTX_SIZE; lits; lia | intros Hnm; destruct (nonmap_low regs L1 s1 mem1 md1 a MID1 Hnm); lia].
- apply WST. lia. }
split; [rewrite (RD 4%bv (SLit TP)) by inlist; reflexivity|].
intros a Ha. apply (writable_ext1 mem1); [| apply ERRW1; exact Ha]. subst mem'. apply HF; [lits; lia | unfold WS, ASF; lits; lia]. }
split; [exact MIDc|]. split; [exact GD|].
split; [intros Hi; rewrite init1 in Hi; discriminate Hi|].
split.
{ exact Hregs. }
split; [exact RF | exact WST].
Qed.
Lemma pgsz_word_mid : forall L1 A1 mm md1, midrep B L1 A1 mm md1 ->
word_mem src0segs mm GOT GUARD /\ word_mem src0segs mm (LIBC + 48) 4096.
Proof.
intros L0 A0 mm md0 HM. pose proof (mid_statics _ _ _ _ _ HM) as ST. split; [exact (st_got _ _ ST) | exact (st_pagesize _ _ ST)].
Qed.
Lemma station_NRs : forall regs1 regs' mm md'' L' s' idx hg am memC,
regs_ok E (ss_regs (ss_NC j)) regs1 ->
regs_preserved regs1 regs' -> getr regs' 10 = Z_to_bv 64 idx ->
facts_ok E (ss_facts callst) ->
region_ok src0segs E memC R_frame -> (forall x, sp - 144 <= x < sp -> mm (Z_to_bv 64 x) = memC (Z_to_bv 64 x)) ->
(forall a, sp - ASF <= a < sp - 144 -> writable_at src0segs mm a) ->
midrep B L' s' mm md'' -> word_mem src0segs mm GUARD g ->
Inv (m :: X) (Some (hg, idx)) U s' -> In m (keys s') -> rawm s' m -> ptr_addr L' m = ptr_addr L1 m ->
active_hd s' j = Some hg -> usedX (m :: X) s' hg am -> 0 <= idx <= 31 ->
exists E', env_agree 64 E E' /\ ew E' 64 = Z_to_bv 64 idx /\ ew E' 80 = Z_to_bv 64 (ptr_addr L' hg) /\ ew E' 81 = Z_to_bv 64 (st_mmap_counter s') /\
st_ok src0segs E' (ss_NRs j) (mkst regs' (Z_to_bv 64 PS_RAS) mm (seg_rom src0segs)).
Proof.
intros regs1 regs' mm md'' L' s' idx hg am memC Hregs PRS RA0 HFacts RF KEEPhi WLO HM GD HI' Km' Mq Eqm Hhd Uhg Hidx.
pose proof facts_N as (HK & Hj & J3 & Hcs & Hfit & Hk & Etot & H23 & Hscj & NN & Hj48 & HKr & Hnu).
pose proof pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7). pose proof (proj1 alloc_ceiling_val) as AC. destruct cs_facts' as (C33 & _).
pose proof (mid_syms _ _ _ _ _ HM) as SO'.
destruct (NR_shapes j J3) as (RSHs & _ & AT64 & MEMs & _ & FC & FAL & _). pose proof (facts_g4 k) as (FG1 & FG2 & FAT).
assert (E33 : ew E 33 = Z_to_bv 64 (csn 33)) by (apply (agree_cs' E 33 HA); lia).
assert (Er2 : ew E 2 = getr regs 2) by (apply (agree_reg' E 2 HA); lia).
assert (U40 : bv_unsigned (ew E 40) = ptr_addr L1 m).
{ rewrite E40. destruct (key_factsR (m :: X) None L1 s1 mem1 md1 m HI1 MID1 Km) as (RB & _). destruct (RB (ptr_addr L1 m) ltac:(unfold META_SIZE; lia)) as (_ & _ & R). apply u64_of_Z. lia. }
pose proof (usedX_MT _ _ _ _ Uhg) as [Mhg NXhg].
assert (Khg : In hg (keys s')) by (apply (MT_Some_In_keys s' hg _ Mhg)).
destruct (key_factsR (m :: X) (Some (hg, idx)) L' s' mm md'' hg HI' HM Khg) as (RBg & ALg & _).
destruct (key_factsR (m :: X) (Some (hg, idx)) L' s' mm md'' m HI' HM Km') as (RBm & ALm & _).
pose proof (inv_ctx HI') as (Cact & _ & _ & _ & _ & _ & _ & _ & Cctr & _).
set (E1 := ewset E 64 (Z_to_bv 64 idx)).
assert (HA1 : env_agree 64 E E1) by (apply env_agree_ewset).
set (base0 := mkSS PS_RAS (sr_set (ss_regs (ss_NC j)) 10 (SOff 64 0)) [] None (mkFacts [] [] [])).
assert (HSI : st_ok src0segs E1 base0 (mkst (regupd regs1 10 (getr regs' 10)) (Z_to_bv 64 PS_RAS) mm (seg_rom src0segs))).
{ unfold st_ok, mkst, base0; cbn. repeat (split; [reflexivity|]). split; [| split; [apply mem_ok_intro; [reflexivity | apply Forall_nil | exact I] | repeat split; apply Forall_nil || exact I]].
apply (regs_ok_set E1 (ss_regs (ss_NC j)) regs1 10 (getr regs' 10) (SOff 64 0)).
- eapply (regs_ok_agree 64 E E1); [exact HA1 | exact AT64 | exact Hregs].
- cbn [sv_denot]. subst E1. rewrite ew_ewset_same, RA0, u64_of_Z, Z.add_0_r by lia. reflexivity. }
assert (AT65 : ss_atoms_lt 65 base0 = true).
{ unfold ss_atoms_lt, base0. cbn [ss_regs ss_mem ss_facts ss_resv mem_atoms_lt facts_atoms_lt forallb f_atoms f_conds f_alias andb].
rewrite (regs_atoms_lt_set 65 (ss_regs (ss_NC j)) 10 (SOff 64 0)); [reflexivity | apply (regs_atoms_lt_mono 64 65); [lia | exact AT64] | reflexivity]. }
assert (NZ : forallb (fun r : reg => negb (bv_eqb r 0)) NR_JUNK = true) by (vm_compute; reflexivity).
assert (EXT : forall r0, ~ In r0 NR_JUNK -> getr regs' r0 = getr (regupd regs1 10 (getr regs' 10)) r0).
{ apply (reg_cases_lit (fun r0 => ~ In r0 NR_JUNK -> getr regs' r0 = getr (regupd regs1 10 (getr regs' 10)) r0)).
intros r0 Hr0 Hnj. cbv [all_regs In] in Hr0.
repeat (destruct Hr0 as [<-|Hr0]; [ first [ solve [exfalso; apply Hnj; inlist]
| reflexivity
| unfold getr, regupd, reg_get; rewrite bvmap_get_set_same; reflexivity
| match goal with |- getr _ ?r = _ =>
let PR := fresh "PR" in let kk := eval vm_compute in (bv_unsigned r) in
assert (PR : getr regs' r = getr regs1 r) by (replace r with (Z_to_bv 5 kk) by (apply bv_eq; reflexivity); apply (PRS kk); unfold callee_saved; lia);
etransitivity; [exact PR | unfold getr, regupd, reg_get; rewrite bvmap_get_set_other by (intros HH; discriminate HH); reflexivity] end ] |]).
destruct Hr0. }
destruct (st_ok_clobber src0segs NR_JUNK 65 E1 _ _ regs' (Z_to_bv 64 PS_RAS) mm (seg_rom src0segs) HSI AT65 NZ EXT) as (En2 & HA2 & HS2).
pose proof HS2 as (_ & _ & _ & _ & _ & _ & RR2 & _). subst base0. cbn [ss_regs ss_pc ss_mem ss_resv ss_facts] in RR2. rewrite RSHs in RR2.
set (E3 := ewset (ewset En2 80 (Z_to_bv 64 (ptr_addr L' hg))) 81 (Z_to_bv 64 (st_mmap_counter s'))).
assert (HA23 : env_agree 80 En2 E3) by (subst E3; apply env_agree_ewset2; lia).
assert (HA3 : env_agree 64 E E3) by (eapply env_agree_trans; [exact HA1 | eapply env_agree_le; [| eapply env_agree_trans; [exact HA2 | eapply env_agree_le; [| exact HA23]]]]; lia).
assert (E3_64 : ew E3 64 = Z_to_bv 64 idx) by (rewrite (proj1 HA23 64%nat), (proj1 HA2 64%nat) by lia; subst E1; apply ew_ewset_same).
assert (E3_80 : ew E3 80 = Z_to_bv 64 (ptr_addr L' hg)) by (subst E3; rewrite ew_ewset_other by lia; apply ew_ewset_same).
assert (E3_81 : ew E3 81 = Z_to_bv 64 (st_mmap_counter s')) by (subst E3; apply ew_ewset_same).
assert (E3_33 : bv_unsigned (ew E3 33) = csn 33) by (rewrite (proj1 HA3 33%nat) by lia; rewrite E33; apply u64_of_Z; lits; lia).
assert (E3_2 : bv_unsigned (ew E3 2) = sp) by (rewrite (proj1 HA3 2%nat) by lia; rewrite Er2; reflexivity).
assert (E3_40 : bv_unsigned (ew E3 40) = ptr_addr L1 m) by (rewrite (proj1 HA3 40%nat) by lia; exact U40).
assert (E3_32 : ew E3 32 = Z_to_bv 64 g) by (rewrite (proj1 HA3 32%nat) by lia; apply (agree_cs' E 32 HA); lia).
exists E3. split; [exact HA3|]. split; [exact E3_64|]. split; [exact E3_80|]. split; [exact E3_81|].
assert (Rm : 4096 <= ptr_addr L1 m /\ ptr_addr L1 m + 40 <= alloc_ceiling /\ (forall x, ptr_addr L1 m <= x < ptr_addr L1 m + 40 -> ~ in_img B x)).
{ unfold META_SIZE in RBm. rewrite Eqm in RBm. destruct (RBm (ptr_addr L1 m) ltac:(lia)) as (_ & _ & R0). destruct (RBm (ptr_addr L1 m + 39) ltac:(lia)) as (_ & _ & R1).
split; [lia|]. split; [lia|]. intros x Hx. exact (proj1 (proj2 (RBm x Hx))). }
destruct Rm as (Rm1 & Rm2 & NIm).
assert (MEM : mem_ok src0segs E3 mm (ss_mem (ss_NRs j))).
{ rewrite MEMs. apply mem_ok_intro.
- destruct J3 as [-> |[-> | ->]]; vm_compute; reflexivity.
- assert (Hhg64 : ptr_addr L' hg + 40 <= alloc_ceiling /\ 4096 <= ptr_addr L' hg) by (destruct (RBg (ptr_addr L' hg) ltac:(unfold META_SIZE; lia)) as (_ & _ & R); unfold META_SIZE in RBg; pose proof (RBg (ptr_addr L' hg + 39) ltac:(lia)); lia).
repeat apply Forall_cons; try apply Forall_nil.
+   apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_hj]; [lits; lia | lits; lia | intros o Ho; lia |].
apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_word src0segs E3 mm 0 (LOCK + 88 + 8 * j) (SOff 80 0) (ptr_addr L' hg)); [apply den_off0; exact E3_80 |].
rewrite Z.add_0_l. pose proof (active_word_mid (m :: X) (Some (hg, idx)) L' s' mm md'' j HI' HM Hj48) as W. rewrite Hhd in W. exact W.
+   apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_ctrN]; [lits; lia | lits; lia | intros o Ho; lia |].
apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_cval src0segs E3 mm 0 (LOCK + 20) 4 (SOff 81 0) (st_mmap_counter s')); [apply den_off0; exact E3_81 | lia |].
intros kk Hkk. rewrite Z.add_0_l. exact (ctr_bytes_mid L' s' mm md'' HM kk Hkk).
+   apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_mslot]; rewrite ?E3_40; [lia | lia | |].
* intros o Ho. apply present_writable. apply (proj1 (RBm (ptr_addr L1 m + o) ltac:(unfold META_SIZE; rewrite Eqm; lia))).
* assert (Z8 : forall off, 0 <= off -> off + 8 <= 40 -> chunk_ok src0segs E3 mm (ptr_addr L1 m) (mkChunk off (CVal 8 (SLit 0)))).
{ intros off H0 H8. apply (chunk_ok_cval src0segs E3 mm (ptr_addr L1 m) off 8 (SLit 0) 0); [reflexivity | lia |].
intros kk Hkk. rewrite <- Eqm, <- Z.add_assoc. rewrite (mslot_zeroR (m :: X) (Some (hg, idx)) L' s' mm md'' m HI' HM Km' Mq) by lia. f_equal. f_equal. unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity. }
assert (Z4 : forall off, 0 <= off -> off + 4 <= 40 -> chunk_ok src0segs E3 mm (ptr_addr L1 m) (mkChunk off (CVal 4 (SLit 0)))).
{ intros off H0 H4. apply (chunk_ok_cval src0segs E3 mm (ptr_addr L1 m) off 4 (SLit 0) 0); [reflexivity | lia |].
intros kk Hkk. rewrite <- Eqm, <- Z.add_assoc. rewrite (mslot_zeroR (m :: X) (Some (hg, idx)) L' s' mm md'' m HI' HM Km' Mq) by lia. f_equal. f_equal. unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity. }
repeat apply Forall_cons; try apply Forall_nil; first [apply Z8; lia | apply Z4; lia].
+   apply (region_ok_ext E3 memC mm R_frame).
* eapply (region_ok_agree _ 64 E E3); [exact HA3 | vm_compute; reflexivity | exact RF].
* cbn [r_chunks R_frame r_base base_val]. rewrite E3_2. intros c i Hin Hi.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]; cbn [c_off c_len cv_len c_val] in Hi |- *; apply KEEPhi; lia.
* cbn [r_base r_wlo r_whi base_val R_frame]. rewrite E3_2. intros o Ho. destruct (Z_lt_le_dec (sp + o) (sp - 144)).
-- apply WLO. unfold ASF in *. lia.
-- apply (writable_ext1 memC); [apply KEEPhi; lia|]. destruct RF as (_ & _ & WF & _). cbn [r_base r_wlo r_whi base_val R_frame] in WF. rewrite Er2 in WF. fold sp in WF. apply WF. exact Ho.
+   apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_got]; [lits; lia | lits; lia | intros o Ho; lia |].
apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_word src0segs E3 mm 0 GOT (SLit GUARD) GUARD); [reflexivity | rewrite Z.add_0_l; exact (proj1 (pgsz_word_mid L' s' mm md'' HM))].
+   apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_guard]; [lits; lia | lits; lia | intros o Ho; lia |].
apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_word src0segs E3 mm 0 GUARD (SOff 32 0) g); [apply den_off0; exact E3_32 | rewrite Z.add_0_l; exact GD].
+   apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_pgsz]; [lits; lia | lits; lia | intros o Ho; lia |].
apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_word src0segs E3 mm 0 (LIBC + 48) (SLit 4096) 4096); [reflexivity | rewrite Z.add_0_l; exact (proj2 (pgsz_word_mid L' s' mm md'' HM))].
+   apply tabs_region_ok. exact (mid_statics _ _ _ _ _ HM).
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [base_val r_base r_lo r_hi R_hj R_ctrN R_mslot R_frame R_got R_guard R_pgsz R_tabs].
rewrite ?E3_40, ?E3_2, ?E3_33.
assert (IMGm : forall lo, in_img B lo -> ~ (ptr_addr L1 m <= lo < ptr_addr L1 m + 40)) by (intros lo Hlo Hr; exact (NIm lo Hr Hlo)).
unfold ASF in *. cbn [cs]. lits.
repeat split; try lia.
all: match goal with
| |- ?h <= ptr_addr L1 m + 0 \/ ptr_addr L1 m + 40 <= ?l =>
destruct (Z_le_dec h (ptr_addr L1 m)); [left; lia|]; destruct (Z_le_dec (ptr_addr L1 m + 40) l); [right; lia|]; exfalso;
destruct (Z_lt_le_dec (ptr_addr L1 m) l);
[apply (IMGm l); [first [apply src0_rwseg_img; lia | apply src0_tabs_img; lits; lia] | lia]
| apply (IMGm (ptr_addr L1 m)); [first [apply src0_rwseg_img; lia | apply src0_tabs_img; lits; lia] | lia]]
| |- ptr_addr L1 m + 40 <= ?l \/ ?h <= ptr_addr L1 m + 0 =>
destruct (Z_le_dec (ptr_addr L1 m + 40) l); [left; lia|]; destruct (Z_le_dec h (ptr_addr L1 m)); [right; lia|]; exfalso;
destruct (Z_lt_le_dec (ptr_addr L1 m) l);
[apply (IMGm l); [first [apply src0_rwseg_img; lia | apply src0_tabs_img; lits; lia] | lia]
| apply (IMGm (ptr_addr L1 m)); [first [apply src0_rwseg_img; lia | apply src0_tabs_img; lits; lia] | lia]]
end. }
assert (FOK : facts_ok E3 facts_NR).
{ rewrite FG2.
apply (facts_ok_add_atom E3 (mkFacts ((80%nat, F_hg) :: (81%nat, F_ctr) :: f_atoms (ss_facts ss_g4)) (f_conds (ss_facts ss_g4)) []) 64 F_idx);
[apply (facts_ok_add_atom E3 (mkFacts ((81%nat, F_ctr) :: f_atoms (ss_facts ss_g4)) (f_conds (ss_facts ss_g4)) []) 80 F_hg);
[apply (facts_ok_add_atom E3 (mkFacts (f_atoms (ss_facts ss_g4)) (f_conds (ss_facts ss_g4)) []) 81 F_ctr)|]|].
- change (mkFacts (f_atoms (ss_facts ss_g4)) (f_conds (ss_facts ss_g4)) []) with facts_NRf. eapply (facts_ok_agree 64 E E3); [exact HA3 | exact FAT |].
unfold callst in HFacts. cbn [ss_facts] in HFacts. rewrite FG1 in HFacts. destruct HFacts as ([_ HAT] & [_ HCO] & _).
split; [exact HAT | split; [exact HCO | exact I]].
- unfold afact_ok, F_ctr. cbn [af_lo af_hi af_al2]. rewrite E3_81, u64_of_Z by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
- assert (Hhg : 4096 <= ptr_addr L' hg /\ ptr_addr L' hg + 40 <= alloc_ceiling).
{ unfold META_SIZE in RBg. destruct (RBg (ptr_addr L' hg) ltac:(lia)) as (_ & _ & R0). destruct (RBg (ptr_addr L' hg + 39) ltac:(lia)) as (_ & _ & R1). lia. }
unfold afact_ok, F_hg. cbn [af_lo af_hi af_al2]. rewrite E3_80, u64_of_Z by lia. change (2 ^ 3) with 8.
split; [lia|]. split; [exact ALg | lia].
- unfold afact_ok, F_idx. cbn [af_lo af_hi af_al2]. rewrite E3_64, u64_of_Z by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
unfold st_ok, mkst; cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem].
pose proof HS2 as (T1 & T2 & T3 & T4 & T5 & T6 & _).
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [eapply (regs_ok_agree 80 En2 E3); [exact HA23 | destruct J3 as [-> |[-> | ->]]; vm_compute; reflexivity | exact RR2] |].
split; [exact MEM | exact FOK].
Qed.
Lemma station_NRf : forall regs1 regs' mm md'' L' s' memC,
regs_ok E (ss_regs (ss_NC j)) regs1 ->
regs_preserved regs1 regs' -> getr regs' 10 = Z_to_bv 64 (2 ^ 64 - 1) ->
facts_ok E (ss_facts callst) ->
region_ok src0segs E memC R_frame -> (forall x, sp - 144 <= x < sp -> mm (Z_to_bv 64 x) = memC (Z_to_bv 64 x)) ->
(forall a, sp - ASF <= a < sp - 144 -> writable_at src0segs mm a) ->
midrep B L' s' mm md'' -> word_mem src0segs mm GUARD g ->
Inv (m :: X) None U s' -> In m (keys s') -> rawm s' m -> ptr_addr L' m = ptr_addr L1 m ->
exists E', env_agree 64 E E' /\
st_ok src0segs E' ss_NRf (mkst regs' (Z_to_bv 64 PS_RAS) mm (seg_rom src0segs)).
Proof.
intros regs1 regs' mm md'' L' s' memC Hregs PRS RA0 HFacts RF KEEPhi WLO HM GD HI' Km' Mq Eqm.
pose proof facts_N as (HK & Hj & J3 & Hcs & Hfit & Hk & Etot & H23 & Hscj & NN & Hj48 & HKr & Hnu).
pose proof pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7). pose proof (proj1 alloc_ceiling_val) as AC. destruct cs_facts' as (C33 & _).
pose proof (mid_syms _ _ _ _ _ HM) as SO'.
destruct (NR_shapes j J3) as (_ & RSHs & AT64 & _ & MEMs & FC & FAL & _). pose proof (facts_g4 k) as (FG1 & FG2 & FAT).
assert (E33 : ew E 33 = Z_to_bv 64 (csn 33)) by (apply (agree_cs' E 33 HA); lia).
assert (Er2 : ew E 2 = getr regs 2) by (apply (agree_reg' E 2 HA); lia).
assert (U40 : bv_unsigned (ew E 40) = ptr_addr L1 m).
{ rewrite E40. destruct (key_factsR (m :: X) None L1 s1 mem1 md1 m HI1 MID1 Km) as (RB & _). destruct (RB (ptr_addr L1 m) ltac:(unfold META_SIZE; lia)) as (_ & _ & R). apply u64_of_Z. lia. }
destruct (key_factsR (m :: X) None L' s' mm md'' m HI' HM Km') as (RBm & ALm & _).
set (E1 := E).
assert (HA1 : env_agree 64 E E1) by (apply env_agree_refl).
set (base0 := mkSS PS_RAS (sr_set (ss_regs (ss_NC j)) 10 (SLit (2 ^ 64 - 1))) [] None (mkFacts [] [] [])).
assert (HSI : st_ok src0segs E1 base0 (mkst (regupd regs1 10 (getr regs' 10)) (Z_to_bv 64 PS_RAS) mm (seg_rom src0segs))).
{ unfold st_ok, mkst, base0; cbn. repeat (split; [reflexivity|]). split; [| split; [apply mem_ok_intro; [reflexivity | apply Forall_nil | exact I] | repeat split; apply Forall_nil || exact I]].
apply (regs_ok_set E1 (ss_regs (ss_NC j)) regs1 10 (getr regs' 10) (SLit (2 ^ 64 - 1))).
- eapply (regs_ok_agree 64 E E1); [exact HA1 | exact AT64 | exact Hregs].
- cbn [sv_denot]. rewrite RA0. reflexivity. }
assert (AT65 : ss_atoms_lt 65 base0 = true).
{ unfold ss_atoms_lt, base0. cbn [ss_regs ss_mem ss_facts ss_resv mem_atoms_lt facts_atoms_lt forallb f_atoms f_conds f_alias andb].
rewrite (regs_atoms_lt_set 65 (ss_regs (ss_NC j)) 10 (SLit (2 ^ 64 - 1))); [reflexivity | apply (regs_atoms_lt_mono 64 65); [lia | exact AT64] | reflexivity]. }
assert (NZ : forallb (fun r : reg => negb (bv_eqb r 0)) NRf_JUNK = true) by (vm_compute; reflexivity).
assert (EXT : forall r0, ~ In r0 NRf_JUNK -> getr regs' r0 = getr (regupd regs1 10 (getr regs' 10)) r0).
{ apply (reg_cases_lit (fun r0 => ~ In r0 NRf_JUNK -> getr regs' r0 = getr (regupd regs1 10 (getr regs' 10)) r0)).
intros r0 Hr0 Hnj. cbv [all_regs In] in Hr0.
repeat (destruct Hr0 as [<-|Hr0]; [ first [ solve [exfalso; apply Hnj; inlist]
| reflexivity
| unfold getr, regupd, reg_get; rewrite bvmap_get_set_same; reflexivity
| match goal with |- getr _ ?r = _ =>
let PR := fresh "PR" in let kk := eval vm_compute in (bv_unsigned r) in
assert (PR : getr regs' r = getr regs1 r) by (replace r with (Z_to_bv 5 kk) by (apply bv_eq; reflexivity); apply (PRS kk); unfold callee_saved; lia);
etransitivity; [exact PR | unfold getr, regupd, reg_get; rewrite bvmap_get_set_other by (intros HH; discriminate HH); reflexivity] end ] |]).
destruct Hr0. }
destruct (st_ok_clobber src0segs NRf_JUNK 65 E1 _ _ regs' (Z_to_bv 64 PS_RAS) mm (seg_rom src0segs) HSI AT65 NZ EXT) as (En2 & HA2 & HS2).
pose proof HS2 as (_ & _ & _ & _ & _ & _ & RR2 & _). subst base0. cbn [ss_regs ss_pc ss_mem ss_resv ss_facts] in RR2. rewrite RSHs in RR2.
set (E3 := En2).
assert (HA23 : env_agree 81 En2 E3) by (apply env_agree_refl).
assert (HA3 : env_agree 64 E E3) by (eapply env_agree_trans; [exact HA1 | eapply env_agree_le; [| eapply env_agree_trans; [exact HA2 | eapply env_agree_le; [| exact HA23]]]]; lia).
assert (E3_33 : bv_unsigned (ew E3 33) = csn 33) by (rewrite (proj1 HA3 33%nat) by lia; rewrite E33; apply u64_of_Z; lits; lia).
assert (E3_2 : bv_unsigned (ew E3 2) = sp) by (rewrite (proj1 HA3 2%nat) by lia; rewrite Er2; reflexivity).
assert (E3_40 : bv_unsigned (ew E3 40) = ptr_addr L1 m) by (rewrite (proj1 HA3 40%nat) by lia; exact U40).
assert (E3_32 : ew E3 32 = Z_to_bv 64 g) by (rewrite (proj1 HA3 32%nat) by lia; apply (agree_cs' E 32 HA); lia).
exists E3. split; [exact HA3|].
assert (Rm : 4096 <= ptr_addr L1 m /\ ptr_addr L1 m + 40 <= alloc_ceiling /\ (forall x, ptr_addr L1 m <= x < ptr_addr L1 m + 40 -> ~ in_img B x)).
{ unfold META_SIZE in RBm. rewrite Eqm in RBm. destruct (RBm (ptr_addr L1 m) ltac:(lia)) as (_ & _ & R0). destruct (RBm (ptr_addr L1 m + 39) ltac:(lia)) as (_ & _ & R1).
split; [lia|]. split; [lia|]. intros x Hx. exact (proj1 (proj2 (RBm x Hx))). }
destruct Rm as (Rm1 & Rm2 & NIm).
assert (MEM : mem_ok src0segs E3 mm (ss_mem ss_NRf)).
{ rewrite MEMs. apply mem_ok_intro.
- vm_compute; reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
+   apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_mslot]; rewrite ?E3_40; [lia | lia | |].
* intros o Ho. apply present_writable. apply (proj1 (RBm (ptr_addr L1 m + o) ltac:(unfold META_SIZE; rewrite Eqm; lia))).
* assert (Z8 : forall off, 0 <= off -> off + 8 <= 40 -> chunk_ok src0segs E3 mm (ptr_addr L1 m) (mkChunk off (CVal 8 (SLit 0)))).
{ intros off H0 H8. apply (chunk_ok_cval src0segs E3 mm (ptr_addr L1 m) off 8 (SLit 0) 0); [reflexivity | lia |].
intros kk Hkk. rewrite <- Eqm, <- Z.add_assoc. rewrite (mslot_zeroR (m :: X) None L' s' mm md'' m HI' HM Km' Mq) by lia. f_equal. f_equal. unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity. }
assert (Z4 : forall off, 0 <= off -> off + 4 <= 40 -> chunk_ok src0segs E3 mm (ptr_addr L1 m) (mkChunk off (CVal 4 (SLit 0)))).
{ intros off H0 H4. apply (chunk_ok_cval src0segs E3 mm (ptr_addr L1 m) off 4 (SLit 0) 0); [reflexivity | lia |].
intros kk Hkk. rewrite <- Eqm, <- Z.add_assoc. rewrite (mslot_zeroR (m :: X) None L' s' mm md'' m HI' HM Km' Mq) by lia. f_equal. f_equal. unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity. }
repeat apply Forall_cons; try apply Forall_nil; first [apply Z8; lia | apply Z4; lia].
+   apply (region_ok_ext E3 memC mm R_frame).
* eapply (region_ok_agree _ 64 E E3); [exact HA3 | vm_compute; reflexivity | exact RF].
* cbn [r_chunks R_frame r_base base_val]. rewrite E3_2. intros c i Hin Hi.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]; cbn [c_off c_len cv_len c_val] in Hi |- *; apply KEEPhi; lia.
* cbn [r_base r_wlo r_whi base_val R_frame]. rewrite E3_2. intros o Ho. destruct (Z_lt_le_dec (sp + o) (sp - 144)).
-- apply WLO. unfold ASF in *. lia.
-- apply (writable_ext1 memC); [apply KEEPhi; lia|]. destruct RF as (_ & _ & WF & _). cbn [r_base r_wlo r_whi base_val R_frame] in WF. rewrite Er2 in WF. fold sp in WF. apply WF. exact Ho.
+   apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_got]; [lits; lia | lits; lia | intros o Ho; lia |].
apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_word src0segs E3 mm 0 GOT (SLit GUARD) GUARD); [reflexivity | rewrite Z.add_0_l; exact (proj1 (pgsz_word_mid L' s' mm md'' HM))].
+   apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_guard]; [lits; lia | lits; lia | intros o Ho; lia |].
apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_word src0segs E3 mm 0 GUARD (SOff 32 0) g); [apply den_off0; exact E3_32 | rewrite Z.add_0_l; exact GD].
+   apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_pgsz]; [lits; lia | lits; lia | intros o Ho; lia |].
apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_word src0segs E3 mm 0 (LIBC + 48) (SLit 4096) 4096); [reflexivity | rewrite Z.add_0_l; exact (proj2 (pgsz_word_mid L' s' mm md'' HM))].
+   apply tabs_region_ok. exact (mid_statics _ _ _ _ _ HM).
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [base_val r_base r_lo r_hi R_mslot R_frame R_got R_guard R_pgsz R_tabs].
rewrite ?E3_40, ?E3_2, ?E3_33.
assert (IMGm : forall lo, in_img B lo -> ~ (ptr_addr L1 m <= lo < ptr_addr L1 m + 40)) by (intros lo Hlo Hr; exact (NIm lo Hr Hlo)).
unfold ASF in *. cbn [cs]. lits.
repeat split; try lia.
all: match goal with
| |- ?h <= ptr_addr L1 m + 0 \/ ptr_addr L1 m + 40 <= ?l =>
destruct (Z_le_dec h (ptr_addr L1 m)); [left; lia|]; destruct (Z_le_dec (ptr_addr L1 m + 40) l); [right; lia|]; exfalso;
destruct (Z_lt_le_dec (ptr_addr L1 m) l);
[apply (IMGm l); [first [apply src0_rwseg_img; lia | apply src0_tabs_img; lits; lia] | lia]
| apply (IMGm (ptr_addr L1 m)); [first [apply src0_rwseg_img; lia | apply src0_tabs_img; lits; lia] | lia]]
| |- ptr_addr L1 m + 40 <= ?l \/ ?h <= ptr_addr L1 m + 0 =>
destruct (Z_le_dec (ptr_addr L1 m + 40) l); [left; lia|]; destruct (Z_le_dec h (ptr_addr L1 m)); [right; lia|]; exfalso;
destruct (Z_lt_le_dec (ptr_addr L1 m) l);
[apply (IMGm l); [first [apply src0_rwseg_img; lia | apply src0_tabs_img; lits; lia] | lia]
| apply (IMGm (ptr_addr L1 m)); [first [apply src0_rwseg_img; lia | apply src0_tabs_img; lits; lia] | lia]]
end. }
assert (FOK : facts_ok E3 facts_NRf).
{ eapply (facts_ok_agree 64 E E3); [exact HA3 | exact FAT |].
unfold callst in HFacts. cbn [ss_facts] in HFacts. rewrite FG1 in HFacts. destruct HFacts as ([_ HAT] & [_ HCO] & _).
split; [exact HAT | split; [exact HCO | exact I]]. }
unfold st_ok, mkst; cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem].
pose proof HS2 as (T1 & T2 & T3 & T4 & T5 & T6 & _).
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [eapply (regs_ok_agree 81 En2 E3); [exact HA23 | vm_compute; reflexivity | exact RR2] |].
split; [exact MEM | exact FOK].
Qed.
Definition NRbase (s' : astate) (L' : layout) (mem' : word -> option byte) (md' : Model) (E' : env) : Prop :=
layout_le s1 L1 L' /\ midrep B L' s' mem' md' /\ ama_ok s' /\ bounded s' /\ rsv_ok s' /\ span_ok s' /\
as_keep (m :: X) s1 s' /\ ub_same s1 s' /\ heads_below s1 s' j /\
(exists vm', md' = with_vmmaps vm' md) /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (sp - stk <= x < sp) -> ~ (ERRNO <= x < ERRNO + 4) -> ~ (CTX <= x < CTX + CTX_SIZE) ->
~ owned B L1 s1 x -> ~ owned B L' s' x -> ~ in_nonmap_region L' s' x -> mem' (Z_to_bv 64 x) = mem1 (Z_to_bv 64 x)) /\
(forall a, (sp - stk <= a < sp - 144 \/ ERRNO <= a < ERRNO + 4) -> writable_at src0segs mem' a) /\
word_mem src0segs mem' GUARD g /\ env_agree 64 E E'.
Definition NRpost (r : Z * astate) (c' : config) : Prop :=
exists L' mem' md' E', c' = mkCfg (mkst (ms_regs (cfg_ms c')) (Z_to_bv 64 PS_RAS) mem' (seg_rom src0segs)) md' /\
NRbase (snd r) L' mem' md' E' /\
((fst r = -1 /\ Inv (m :: X) None U (snd r) /\ st_ok src0segs E' ss_NRf (cfg_ms c')) \/
(0 <= fst r /\ ew E' 64 = Z_to_bv 64 (fst r) /\
exists hg am, Inv (m :: X) (Some (hg, fst r)) U (snd r) /\ active_hd (snd r) j = Some hg /\ usedX (m :: X) (snd r) hg am /\
am_sc am = j /\ total + IB <= stride_of am /\ fst r <= am_last am /\
ew E' 80 = Z_to_bv 64 (ptr_addr L' hg) /\ ew E' 81 = Z_to_bv 64 (st_mmap_counter (snd r)) /\ st_ok src0segs E' (ss_NRs j) (cfg_ms c'))).
Theorem call_nest : forall c, NCpost c -> mreal src0segs c (alloc_slot fuel j total s1) NRpost.
Proof.
intros c (ms & -> & HS & HF).
pose proof facts_N as (HK & Hj & J3 & Hcs & Hfit & Hk & Etot & H23 & Hscj & NN & Hj48 & HKr & Hnu).
pose proof pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7). pose proof (proj1 alloc_ceiling_val) as AC.
destruct (call_facts ms HS HF) as (Ems & R1 & SPZ & R2 & R10' & R11' & PRE1 & MIDc & GDc & AUX1 & Hregs & RF & WST).
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & HFacts).
assert (RSV1 : rsv_ok s1) by exact (rsv_ok_xfer X U A regs HI XR RSV (m :: X) s1 HI1 XC1n (fun q am Hu => proj1 (US1 q am) Hu)).
assert (SPOK1 : span_ok s1) by exact (span_ok_xfer X A SPOK (m :: X) s1 XC1n (fun q am Hu => proj1 (US1 q am) Hu)).
assert (Htot : 0 <= total < MMAP_THRESHOLD) by (pose proof (class_size_bounds j Hj48); unfold MMAP_THRESHOLD, IB in *; lia).
assert (Hstk' : ASF <= stk - 144 <= AS_STACK) by (pose proof (as_budget_range j ltac:(lia)); pose proof (as_budget_step sc j H23 ltac:(lia)); unfold ASF in *; lia).
assert (HB' : as_budget j <= stk - 144) by (pose proof (as_budget_step sc j H23 ltac:(lia)); lia).
assert (HN' : (need j <= fuel)%nat) by lia.
rewrite Ems.
pose proof (IH (m :: X) U L1 s1 (ms_regs ms) (ms_mem ms) md1 j total (stk - 144) g HI1 rawX1 AMA1 BND1 RSV1 SPOK1 Hj48 Htot MIDc AUX1 PRE1 Hstk' R10' R11' GDc HU HB' HN') as M.
pose proof (proj1 (alloc_mutual fuel) (m :: X) U s1 j total (slot_post (m :: X) U s1 j total) HI1 Hj48 ltac:(lia) Hfit HN' (fun r Hr => Hr)) as SP.
pose proof (mreal_itok _ _ _ _ _ M SP) as M2.
eapply mreal_mono; [| exact M2]. cbv beta.
intros r c' [(L' & regs' & mem'' & md'' & -> & MID' & AMA' & BND' & RSV' & SPOK' & LE' & PRS & VM' & FR' & SCR' & RA0 & UZ & AK' & GD') (HBel & UB & CASES)].
cbn [cfg_ms ms_regs].
rewrite SPZ in FR', SCR'. rewrite R1.
assert (Km' : In m (keys (snd r))) by (destruct CASES as [[_ HI'] | [_ (hg & am & HI' & _)]]; exact (proj1 (inv_X HI' m (or_introl eq_refl)))).
assert (Mq : rawm (snd r) m) by (destruct AK' as (K1 & _); apply (K1 m (or_introl eq_refl)); exact Mm).
assert (Eqm : ptr_addr L' m = ptr_addr L1 m).
{ destruct (key_factsR (m :: X) None L1 s1 mem1 md1 m HI1 MID1 Km) as (_ & _ & _ & _ & PR). destruct LE' as (_ & _ & _ & Y4).
unfold ptr_addr. rewrite !loc_addr_LMem, (Y4 (prid m) PR). reflexivity. }
assert (EASF : ASF = 384) by reflexivity.
assert (KEEPhi : forall x, sp - 144 <= x < sp -> mem'' (Z_to_bv 64 x) = ms_mem ms (Z_to_bv 64 x)).
{ intros x Hx. apply (FR' x ltac:(lia)).
- change (ms_ctx B) with CTX. unfold CTX_SIZE. lits. lia.
- intros Ho. pose proof (owned_low_mid (m :: X) None L1 s1 (ms_mem ms) md1 x HI1 MIDc Ho). lia.
- intros Ho. destruct CASES as [[_ HI'] | [_ (hg & am & HI' & _)]]; pose proof (owned_low_mid (m :: X) _ L' (snd r) mem'' md'' x HI' MID' Ho); lia.
- intros Hn'. destruct (nonmap_low regs L' (snd r) mem'' md'' x MID' Hn'). lia.
- unfold call_scratch. change (errno_addr B) with ERRNO. lits. lia. }
assert (WLO : forall a, sp - ASF <= a < sp - 144 -> writable_at src0segs mem'' a).
{ intros a Ha. rewrite <- B_segs. apply SCR'. unfold call_scratch. left. unfold ASF in Ha. lia. }
assert (BASE : forall E', env_agree 64 E E' -> NRbase (snd r) L' mem'' md'' E').
{ intros E' HAE. unfold NRbase. split; [exact LE'|]. split; [exact MID'|]. split; [exact AMA'|]. split; [exact BND'|]. split; [exact RSV'|]. split; [exact SPOK'|].
split; [exact AK'|]. split; [exact UB|]. split; [exact HBel|]. split.
{ destruct VM' as [vm' ->]. destruct VM1 as [vm1 ->]. exists vm'. apply YN2d.with_vmmaps_twice. }
split.
{ intros x Hx Ns Ne Nc No No' Nn. rewrite (FR' x Hx); [apply HF; [exact Hx | unfold WS, ASF; lia] | change (ms_ctx B) with CTX; exact Nc | exact No | exact No' | exact Nn |].
unfold call_scratch. change (errno_addr B) with ERRNO. lia. }
split; [| split; [exact GD' | exact HAE]].
intros a Ha. rewrite <- B_segs. apply SCR'. unfold call_scratch. change (errno_addr B) with ERRNO. lia. }
destruct CASES as [[Hm1 HI'] | [Hge (hg & am & HI' & Hhd & Uhg & Hsc' & Hfit' & Hidx)]].
-
cbn [fst] in Hm1. rewrite Hm1 in RA0.
destruct (station_NRf (ms_regs ms) regs' mem'' md'' L' (snd r) (ms_mem ms) Hregs PRS ltac:(rewrite RA0; apply bv_eq; reflexivity) HFacts RF KEEPhi WLO MID' GD' HI' Km' Mq Eqm) as (E' & HAE & HS').
exists L', mem'', md'', E'. split; [reflexivity|]. split; [exact (BASE E' HAE)|]. left. split; [exact Hm1|]. split; [exact HI' | exact HS'].
-
pose proof (inv_groups HI' hg am Uhg) as ((Mlast & _) & _).
destruct (station_NRs (ms_regs ms) regs' mem'' md'' L' (snd r) (fst r) hg am (ms_mem ms) Hregs PRS RA0 HFacts RF KEEPhi WLO MID' GD' HI' Km' Mq Eqm Hhd Uhg ltac:(lia)) as (E' & HAE & E64 & E80 & E81 & HS').
exists L', mem'', md'', E'. split; [reflexivity|]. split; [exact (BASE E' HAE)|]. right. split; [exact Hge|]. split; [exact E64|].
exists hg, am. split; [exact HI'|]. split; [exact Hhd|]. split; [exact Uhg|]. split; [exact Hsc'|]. split; [exact Hfit'|]. split; [exact Hidx|].
split; [exact E80|]. split; [exact E81 | exact HS'].
Qed.
Section NB.
Variables (sq : astate) (L' : layout) (mem' : word -> option byte) (md' : Model) (E' : env).
Hypothesis NRB : NRbase sq L' mem' md' E'.
Hypothesis HIq : Inv (m :: X) None U sq.
Let Mhq : m_halted md' = None := proj1 (mid_md _ _ _ _ _ (proj1 (proj2 NRB))).
Let Mlzq : m_vm_lazy md' = [] := proj1 (proj2 (mid_md _ _ _ _ _ (proj1 (proj2 NRB)))).
Lemma sq_facts : layout_le s1 L1 L' /\ midrep B L' sq mem' md' /\ ama_ok sq /\ bounded sq /\ rsv_ok sq /\ span_ok sq /\
as_keep (m :: X) s1 sq /\ ub_same s1 sq /\ heads_below s1 sq j /\ (exists vm', md' = with_vmmaps vm' md) /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (sp - stk <= x < sp) -> ~ (ERRNO <= x < ERRNO + 4) -> ~ (CTX <= x < CTX + CTX_SIZE) ->
~ owned B L1 s1 x -> ~ owned B L' sq x -> ~ in_nonmap_region L' sq x -> mem' (Z_to_bv 64 x) = mem1 (Z_to_bv 64 x)) /\
(forall a, (sp - stk <= a < sp - 144 \/ ERRNO <= a < ERRNO + 4) -> writable_at src0segs mem' a) /\
word_mem src0segs mem' GUARD g /\ env_agree 64 E E' /\
Xclean (m :: X) sq /\ In m (keys sq) /\ rawm sq m /\ ptr_addr L' m = ptr_addr L1 m /\ rawX X sq /\ env_agree 40 E00 E' /\ ew E' 40 = Z_to_bv 64 (ptr_addr L1 m).
Proof.
pose proof NRB as (LE' & MID' & AMA' & BND' & RSV' & SPOK' & AK' & UB & HBel & VM' & FR' & SCR' & GD' & HAE).
assert (RXq : rawX (m :: X) sq) by exact (rawX_keep (m :: X) s1 sq rawX1 AK').
repeat (split; [assumption|]). split.
{ intros x am Hx Hu. destruct (RXq x Hx) as [Mq|Mq]; rewrite Mq in Hu; discriminate. }
split; [exact (proj1 (inv_X HIq m (or_introl eq_refl)))|].
split; [exact (RXq m (or_introl eq_refl))|].
split.
{ destruct (key_factsR (m :: X) None L1 s1 mem1 md1 m HI1 MID1 Km) as (_ & _ & _ & _ & PR). destruct LE' as (_ & _ & _ & Y4).
unfold ptr_addr. rewrite !loc_addr_LMem, (Y4 (prid m) PR). reflexivity. }
split; [intros x Hx; exact (RXq x (or_intror Hx))|].
split; [eapply env_agree_trans; [exact HA | eapply env_agree_le; [| exact HAE]; lia]|].
rewrite (proj1 HAE 40%nat) by lia. exact E40.
Qed.
Lemma fm_shapeN : exists ms sf,
ring_ok (flinks (m :: X) sq) (st_free_meta_head sq) ms /\
(forall q, In q ms -> exists qp qn, MT sq q = Some (MFree qp qn) /\ memb q (m :: X) = false) /\
~ In m ms /\
(forall h0 rest, ms = h0 :: rest -> exists hn, MT sq h0 = Some (MFree (Some (last ms m)) hn)) /\
free_meta m sq = IRet (tt, sf) /\ fm_post sq m ms sf /\
Inv X None U sf /\ (forall q am, usedX X sf q am <-> usedX (m :: X) sq q am) /\ rawX X sf /\ ama_ok sf /\ bounded sf /\
st_regions sf = st_regions sq /\ st_areas sf = st_areas sq /\ as_keep X A sf /\ rsv_ok sf /\ span_ok sf /\ used_metas sf = used_metas sq.
Proof.
pose proof sq_facts as (LE' & MID' & AMA' & BND' & RSV' & SPOK' & AK' & UB & HBel & VM' & FR' & SCR' & GD' & HAE & XCq & Kmq & Mq & Eqm & RXq & HA' & E40').
destruct (fm_shape X U sq m HIq) as (ms & sf & FRg & MEMS & Hmn & HD0 & Efm & FP). exists ms, sf.
assert (SPEC : itok (free_meta m sq) (fun r => Inv (remove sptr_eq_dec m (m :: X)) None U (snd r) /\ (forall q am, usedX (remove sptr_eq_dec m (m :: X)) (snd r) q am <-> usedX (m :: X) sq q am))).
{ apply (free_meta_spec (m :: X) None U sq m); [exact HIq | left; reflexivity |]. intros s'' HI'' _ _ EU _. split; [exact HI'' | exact EU]. }
rewrite Efm in SPEC. cbn [itok snd] in SPEC. destruct SPEC as [HI' EU'].
assert (RM : remove sptr_eq_dec m (m :: X) = X).
{ cbn. destruct (sptr_eq_dec m m) as [_|NE]; [| exfalso; apply NE; reflexivity]. apply notin_remove. intros Hin. apply (proj2 (memb_In m X)) in Hin. rewrite NXm in Hin. discriminate. }
rewrite RM in HI', EU'.
pose proof FP as (SB & EA & Hhd & MTm & MTo & MTr).
pose proof SB as (Sid & Smc & Sam & Samc & Saac & Ssh & Sah & Sat & Sama & Su & Suq & Sb & Ssq & Sbrk & Srg & Sar & Sk).
assert (RXs : rawX X sf).
{ intros x Hx. rewrite MTo; [exact (RXq x Hx)|]. intros [<-|Hin]; [apply (proj2 (memb_In _ X)) in Hx; rewrite NXm in Hx; discriminate|].
destruct (MEMS x Hin) as (qp & qn & _ & Mx). cbn [memb existsb] in Mx. apply Bool.orb_false_iff in Mx as [_ Mx]. change (memb x X = false) in Mx.
apply (proj2 (memb_In x X)) in Hx. rewrite Hx in Mx. discriminate. }
assert (UM : used_metas sf = used_metas sq).
{ apply used_metas_ext; [exact (proj1 (inv_keys HIq)) | exact Sk |]. intros q.
destruct (sptr_eq_dec q m) as [->|Hqm]; [right; rewrite MTm; destruct Mq as [Eq1|Eq1]; rewrite Eq1; split; reflexivity|].
destruct (In_dec sptr_eq_dec q ms) as [Hq|Hq].
- right. destruct (MEMS q Hq) as (qp & qn & Mq' & _). rewrite (MTr q _ Hq Mq'), Mq'. cbn. split; reflexivity.
- left. apply MTo. intros [Eq1|Eq1]; [exact (Hqm (eq_sym Eq1)) | exact (Hq Eq1)]. }
split; [exact FRg|]. split; [exact MEMS|]. split; [exact Hmn|]. split; [exact HD0|]. split; [exact Efm|]. split; [exact FP|]. split; [exact HI'|]. split; [exact EU'|]. split; [exact RXs|]. split.
- unfold ama_ok. rewrite Sar, Sama, Srg. exact AMA'.
- split; [| split; [exact Srg | split; [exact Sar | split; [| split; [| split; [| exact UM]]]]]].
+ destruct BND' as (B1 & B2 & B3'). unfold bounded, usage_of in *. rewrite Su, Ssh, Sar. exact (conj B1 (conj B2 B3')).
+ eapply as_keep_trans; [exact AK1|]. eapply as_keep_trans; [exact (as_keep_cons m X s1 sq AK')|]. apply as_keep_same; [| exact Sar | exact Srg].
intros x Hx _. exact (RXs x Hx).
+ intros g' am i fr Hin Hk. unfold frames in Hin. rewrite UM in Hin. exact (RSV' g' am i fr Hin Hk).
+ intros g' am Hg' Hlt. apply (SPOK' g' am); [| exact Hlt].
destruct (sptr_eq_dec g' m) as [->|Hg'm]; [rewrite MTm in Hg'; discriminate|].
destruct (In_dec sptr_eq_dec g' ms) as [Hq|Hq].
* destruct (MEMS g' Hq) as (qp & qn & Mq' & _). rewrite (MTr g' _ Hq Mq') in Hg'. discriminate.
* rewrite <- (MTo g'); [exact Hg'|]. intros [Eq1|Eq1]; [exact (Hg'm (eq_sym Eq1)) | exact (Hq Eq1)].
Qed.
Lemma key_rangeq : forall q x, In q (keys sq) -> ptr_addr L' q <= x < ptr_addr L' q + 40 -> ~ in_img B x /\ 4096 <= x < alloc_ceiling /\ present mem' x.
Proof.
intros q x Hq Hx. pose proof sq_facts as (_ & MID' & _).
destruct (key_factsR (m :: X) None L' sq mem' md' q HIq MID' Hq) as (RB & _). destruct (RB x Hx) as (P & NI & R). exact (conj NI (conj R P)).
Qed.
Lemma key_presentq : forall mm q x, midrep B L' sq mm md' -> In q (keys sq) -> ptr_addr L' q <= x < ptr_addr L' q + 40 -> present mm x.
Proof. intros mm q x HM Hq Hx. destruct (key_factsR (m :: X) None L' sq mm md' q HIq HM Hq) as (RB & _). exact (proj1 (RB x Hx)). Qed.
Lemma keys_apartq : forall p q, In p (keys sq) -> In q (keys sq) -> p <> q -> ptr_addr L' p + 40 <= ptr_addr L' q \/ ptr_addr L' q + 40 <= ptr_addr L' p.
Proof.
intros p q Hp Hq Hne. pose proof sq_facts as (_ & MID' & _).
exact (YN0i.keys_apart (m :: X) None U L' sq regs mem' md' HIq MID' p q Hp Hq Hne).
Qed.
Lemma key_slot_areaq : forall q x, In q (keys sq) -> ptr_addr L' q <= x < ptr_addr L' q + 40 ->
exists a, In a (st_areas sq) /\ ptr_addr L' a <= x < ptr_addr L' a + PGSZ.
Proof.
intros q x Hq Hx. pose proof sq_facts as (_ & MID' & _).
destruct (key_factsR (m :: X) None L' sq mem' md' q HIq MID' Hq) as (_ & _ & _ & (a & kk & Ha & Hk & Eq) & _).
exists a. split; [exact Ha|]. rewrite Eq in Hx. unfold slot_of in Hx. rewrite ptr_addr_padd in Hx. unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. lia.
Qed.
Lemma key_nonmapq : forall q x, In q (keys sq) -> ptr_addr L' q <= x < ptr_addr L' q + 40 -> in_nonmap_region L' sq x.
Proof.
intros q x Hq Hx. pose proof sq_facts as (_ & MID' & _). destruct (key_slot_areaq q x Hq Hx) as (a & Ha & Hax).
apply (area_nonmap B (m :: X) None U L' sq mem' md' HIq MID' sq L' a x Ha Hax).
- intros kk rg Hk Hl Hkd. exists rg. repeat split; try assumption. lia.
- intros kk rg Hk _ _. exact Hk.
- intros; reflexivity.
Qed.
Definition SKn0 : list (option nat * Z * Z) := [(Some 40%nat, 0, 40); (Some 2%nat, -ASF, 0)].
Definition WDn0 (x : Z) : Prop := WSn x \/ ptr_addr L1 m <= x < ptr_addr L1 m + 40.
Definition SKn1 : list (option nat * Z * Z) := (None, LOCK + 24, LOCK + 32) :: SKn0.
Definition WDn1 (x : Z) : Prop := WDn0 x \/ LOCK + 24 <= x < LOCK + 32.
Definition SKn2 : list (option nat * Z * Z) := (Some 87%nat, 0, 8) :: (Some 88%nat, 8, 16) :: SKn1.
Definition WDn2 (h0 hp : Z) (x : Z) : Prop := WDn1 x \/ h0 <= x < h0 + 8 \/ hp + 8 <= x < hp + 16.
Lemma SKn0_WDn0 : forall Ex b lo hi x, env_agree 40 E00 Ex -> ew Ex 40 = Z_to_bv 64 (ptr_addr L1 m) ->
In (b, lo, hi) SKn0 -> base_val Ex b + lo <= x < base_val Ex b + hi -> WDn0 x.
Proof.
intros Ex b lo hi x HAx Ex40 Hin Hx. pose proof sq_facts as (_ & MID' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Kmq & _ & Eqm & _).
assert (U40 : bv_unsigned (ew Ex 40) = ptr_addr L1 m).
{ pose proof (proj1 alloc_ceiling_val). rewrite Ex40. destruct (key_rangeq m (ptr_addr L' m) Kmq ltac:(lia)) as (_ & R & _). rewrite Eqm in R. apply u64_of_Z. lia. }
unfold SKn0 in Hin. cbn [In] in Hin. unfold WDn0.
destruct Hin as [H|[H|[]]]; injection H as <- <- <-; cbn [base_val] in Hx.
- right. rewrite U40 in Hx. lia.
- left. exact (YN13.win_stack L A regs sc g j1 j2 s1 Ex x HAx Hx).
Qed.
Lemma SKn1_WDn1 : forall Ex b lo hi x, env_agree 40 E00 Ex -> ew Ex 40 = Z_to_bv 64 (ptr_addr L1 m) ->
In (b, lo, hi) SKn1 -> base_val Ex b + lo <= x < base_val Ex b + hi -> WDn1 x.
Proof.
intros Ex b lo hi x HAx Ex40 Hin Hx. unfold SKn1 in Hin. cbn [In] in Hin. unfold WDn1.
destruct Hin as [H|Hin]; [injection H as <- <- <-; cbn [base_val] in Hx; right; lia |].
left. exact (SKn0_WDn0 Ex b lo hi x HAx Ex40 Hin Hx).
Qed.
Lemma SKn2_WDn2 : forall Ex b lo hi x h0 hp, env_agree 40 E00 Ex -> ew Ex 40 = Z_to_bv 64 (ptr_addr L1 m) ->
bv_unsigned (ew Ex 87) = h0 -> bv_unsigned (ew Ex 88) = hp ->
In (b, lo, hi) SKn2 -> base_val Ex b + lo <= x < base_val Ex b + hi -> WDn2 h0 hp x.
Proof.
intros Ex b lo hi x h0 hp HAx Ex40 E87 E88 Hin Hx. unfold SKn2 in Hin. cbn [In] in Hin. unfold WDn2.
destruct Hin as [H|[H|Hin]]; [injection H as <- <- <-; cbn [base_val] in Hx; rewrite E87 in Hx; right; left; lia
| injection H as <- <- <-; cbn [base_val] in Hx; rewrite E88 in Hx; right; right; lia |].
left. exact (SKn1_WDn1 Ex b lo hi x HAx Ex40 Hin Hx).
Qed.
Lemma frame_keepN : forall (W : Z -> Prop) Ex rs sk mm mm' mm0,
frame_of Ex rs mm mm' -> wsub rs sk = true ->
(forall b lo hi x, In (b, lo, hi) sk -> base_val Ex b + lo <= x < base_val Ex b + hi -> W x) ->
(forall x, 0 <= x < 2 ^ 64 -> ~ W x -> mm (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x)) ->
forall x, 0 <= x < 2 ^ 64 -> ~ W x -> mm' (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x).
Proof.
intros W Ex rs sk mm mm' mm0 Hfr WSB HW HF x Hx Hw. rewrite <- (HF x Hx Hw). apply (frame_of_at Ex _ _ _ x Hfr Hx). intros Hin.
destruct (in_wrange_wsub regs Ex _ sk x WSB Hin) as (b & lo & hi & Hl & Hx'). exact (Hw (HW b lo hi x Hl Hx')).
Qed.
Lemma skelsN : wsub (ss_mem ss_NRf) SKn0 = true /\ wsub (ss_mem ss_NF1) SKn1 = true /\ wsub (ss_mem (add_cond ss_nf1 C_fe)) SKn1 = true /\
wsub (ss_mem (add_cond ss_nf1 C_fne)) SKn1 = true /\ wsub (ss_mem ss_NF2) SKn2 = true /\
ss_atoms_lt 87 ss_nf0 = true /\ ss_atoms_lt 88 ss_nf2 = true /\
map (fun r => (r_base r, r_lo r, r_hi r)) (ss_mem ss_nf0) = [(Some 40%nat, 0, 40); (Some 2%nat, -ASF, 0); (None, GOT, GOT + 8); (None, GUARD, GUARD + 8); (None, LIBC + 48, LIBC + 56); (None, DEB, DEB + 159)] /\
map (fun r => (r_base r, r_lo r, r_hi r)) (ss_mem ss_nf2) = (None, LOCK + 24, LOCK + 32) :: [(Some 40%nat, 0, 40); (Some 2%nat, -ASF, 0); (None, GOT, GOT + 8); (None, GUARD, GUARD + 8); (None, LIBC + 48, LIBC + 56); (None, DEB, DEB + 159)] /\
ss_NF1 = mkSS (ss_pc ss_nf0) (ss_regs ss_nf0) (R_fmh :: ss_mem ss_nf0) None (addfact 87 F_ptr0 (ss_facts ss_nf0)) /\
ss_NF2 = mkSS (ss_pc ss_nf2) (ss_regs ss_nf2) (R_hd :: R_hp :: ss_mem ss_nf2) None (addfact 88 F_ptr0 (ss_facts ss_nf2)).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma finals_nfN : finalS_check ss_nfeE (SLit (2 ^ 64 - 1)) = true /\ finalS_check ss_nfneE (SLit (2 ^ 64 - 1)) = true /\
(exists rstk, nth_error (ss_mem ss_nfeE) 2 = Some rstk /\ r_base rstk = Some 2%nat /\ r_wlo rstk = - ASF /\ r_whi rstk = 0) /\
(exists rstk, nth_error (ss_mem ss_nfneE) 4 = Some rstk /\ r_base rstk = Some 2%nat /\ r_wlo rstk = - ASF /\ r_whi rstk = 0) /\
nth_error (ss_mem ss_nfeE) 4 = Some R_guard /\ nth_error (ss_mem ss_nfneE) 6 = Some R_guard /\
nth_error (ss_mem ss_nfeE) 0 = Some (YP09.mkRegion None (LOCK + 24) (LOCK + 32) (LOCK + 24) (LOCK + 32) [mkChunk (LOCK + 24) (CVal 8 (SOff 40 0))]) /\
nth_error (ss_mem ss_nfeE) 1 = Some (YP09.mkRegion (Some 40%nat) 0 40 0 40 [mkChunk 8 (CVal 8 (SOff 40 0)); mkChunk 0 (CVal 8 (SOff 40 0)); mkChunk 16 (CVal 8 (SLit 0)); mkChunk 24 (CVal 8 (SLit 0)); mkChunk 32 (CVal 8 (SLit 0))]) /\
nth_error (ss_mem ss_nfneE) 0 = Some (YP09.mkRegion (Some 87%nat) 0 8 0 8 [mkChunk 0 (CVal 8 (SOff 40 0))]) /\
nth_error (ss_mem ss_nfneE) 1 = Some (YP09.mkRegion (Some 88%nat) 8 16 8 16 [mkChunk 8 (CVal 8 (SOff 40 0))]) /\
nth_error (ss_mem ss_nfneE) 2 = Some (YP09.mkRegion None (LOCK + 24) (LOCK + 32) (LOCK + 24) (LOCK + 32) [mkChunk (LOCK + 24) (CVal 8 (SOff 87 0))]) /\
nth_error (ss_mem ss_nfneE) 3 = Some (YP09.mkRegion (Some 40%nat) 0 40 0 40 [mkChunk 0 (CVal 8 (SOff 88 0)); mkChunk 8 (CVal 8 (SOff 87 0)); mkChunk 16 (CVal 8 (SLit 0)); mkChunk 24 (CVal 8 (SLit 0)); mkChunk 32 (CVal 8 (SLit 0))]).
Proof. vm_compute. repeat (split; [first [reflexivity | eexists; repeat split; reflexivity]|]). reflexivity. Qed.
Definition fmhN : Z := onum L' (st_free_meta_head sq).
Let E8 : env := ewset E' 87 (Z_to_bv 64 fmhN).
Lemma fmhN_facts : 0 <= fmhN <= alloc_ceiling - 40 /\ fmhN mod 8 = 0 /\
(forall mm, midrep B L' sq mm md' -> word_mem src0segs mm (LOCK + 24) fmhN) /\
(forall h, st_free_meta_head sq = Some h -> fmhN = ptr_addr L' h /\ In h (keys sq)).
Proof.
pose proof (proj1 alloc_ceiling_val) as AC. pose proof sq_facts as (_ & MID' & _).
assert (W : forall mm, midrep B L' sq mm md' -> word_mem src0segs mm (LOCK + 24) fmhN).
{ intros mm HM. replace (LOCK + 24) with (CTX + CTX_free_meta_head) by (lits; unfold CTX_free_meta_head; lia). unfold fmhN.
replace (onum L' (st_free_meta_head sq)) with (sval_num L' (optr (st_free_meta_head sq))) by (destruct (st_free_meta_head sq); reflexivity).
apply (ctx_word_mid L' sq mm md' CTX_free_meta_head (optr (st_free_meta_head sq)) HM); [| destruct (st_free_meta_head sq); intros z; discriminate].
unfold ctx_cells. apply in_app_iff. left. do 3 right. left. reflexivity. }
destruct (inv_rings HIq) as ((ms & FRg & _) & _).
destruct (st_free_meta_head sq) as [h|] eqn:Eh.
- destruct (ring_head_In _ _ _ FRg) as [Hin _]. destruct (fring_members_free _ _ _ _ h FRg Hin) as (pr & nx & _ & Mh).
pose proof (In_keys_of_MT _ _ _ Mh) as Kh. destruct (key_factsR (m :: X) None L' sq mem' md' h HIq MID' Kh) as (RB & AL & _).
unfold fmhN. rewrite Eh. cbn [onum]. destruct (RB (ptr_addr L' h) ltac:(unfold META_SIZE; lia)) as (_ & _ & R). destruct (RB (ptr_addr L' h + 39) ltac:(unfold META_SIZE; lia)) as (_ & _ & R').
split; [lia|]. split; [exact AL|]. split; [unfold fmhN in W; rewrite Eh in W; exact W|]. intros h' Hh'. injection Hh' as <-. split; [reflexivity | exact Kh].
- unfold fmhN in *. rewrite Eh in *. cbn [onum] in *. split; [lia|]. split; [reflexivity|]. split; [exact W|]. intros h' Hh'. discriminate.
Qed.
Lemma apart_nf : forall Ex lo hi r, env_agree 40 E00 Ex -> ew Ex 40 = Z_to_bv 64 (ptr_addr L1 m) -> lo < hi ->
(forall x, lo <= x < hi -> ~ in_img B x /\ x < alloc_ceiling) -> (hi <= ptr_addr L1 m \/ ptr_addr L1 m + 40 <= lo) ->
In (r_base r, r_lo r, r_hi r) ((None, LOCK + 24, LOCK + 32) :: [(Some 40%nat, 0, 40); (Some 2%nat, -ASF, 0); (None, GOT, GOT + 8); (None, GUARD, GUARD + 8); (None, LIBC + 48, LIBC + 56); (None, DEB, DEB + 159)]) ->
hi <= base_val Ex (r_base r) + r_lo r \/ base_val Ex (r_base r) + r_hi r <= lo.
Proof.
intros Ex lo hi r HAx Ex40 Hlh Hoff Hm Hin. pose proof (proj1 alloc_ceiling_val) as AC. pose proof pre_facts' as (_ & _ & P3 & _).
pose proof sq_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Kmq & _ & Eqm & _).
assert (U40 : bv_unsigned (ew Ex 40) = ptr_addr L1 m).
{ rewrite Ex40. destruct (key_rangeq m (ptr_addr L' m) Kmq ltac:(lia)) as (_ & R & _). rewrite Eqm in R. apply u64_of_Z. lia. }
assert (IMG : forall a b, (forall x, a <= x < b -> in_img B x) -> a < b -> hi <= a \/ b <= lo).
{ intros a b Hab Hlt. destruct (Z_lt_le_dec lo a) as [H1|H1].
- destruct (Z_le_dec hi a); [left; lia|]. exfalso. exact (proj1 (Hoff a ltac:(lia)) (Hab a ltac:(lia))).
- destruct (Z_le_dec b lo); [right; lia|]. exfalso. exact (proj1 (Hoff lo ltac:(lia)) (Hab lo ltac:(lia))). }
cbn [In] in Hin.
destruct Hin as [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; apply (f_equal (fun t => match t with (b, l, h) => (b, l, h) end)) in H; cbn in H; injection H as X1 X2 X3; rewrite <- X1, <- X2, <- X3; cbn [base_val].
- lits. apply IMG; [intros x Hx; apply src0_rwseg_img; lia | lia].
- rewrite U40. lia.
- rewrite (agree_reg' Ex 2 HAx) by lia. replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : reg) by (apply bv_eq; reflexivity). fold sp. left.
destruct (Z_le_dec hi (sp + - ASF)); [lia|]. exfalso. pose proof (Hoff (hi - 1) ltac:(lia)). unfold ASF in *. lia.
- lits. apply IMG; [intros x Hx; apply src0_rwseg_img; lia | lia].
- lits. apply IMG; [intros x Hx; apply src0_rwseg_img; lia | lia].
- lits. apply IMG; [intros x Hx; apply src0_rwseg_img; lia | lia].
- apply IMG; [intros x Hx; apply src0_tabs_img; lia | lia].
Qed.
Lemma station_NF1 : forall ms0 mm0, st_ok src0segs E' ss_nf0 ms0 -> midrep B L' sq mm0 md' ->
(forall x, 0 <= x < 2 ^ 64 -> ~ WDn0 x -> ms_mem ms0 (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x)) ->
st_ok src0segs E8 ss_NF1 ms0 /\ env_agree 87 E' E8 /\ env_agree 40 E00 E8 /\ ew E8 87 = Z_to_bv 64 fmhN /\ ew E8 40 = Z_to_bv 64 (ptr_addr L1 m).
Proof.
intros ms0 mm0 HS HM F0. pose proof (proj1 alloc_ceiling_val) as AC. destruct pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
pose proof sq_facts as (_ & MID' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Kmq & _ & Eqm & _ & HA' & E40').
destruct cs_facts' as (C33 & _). pose proof fmhN_facts as (Hr & Hal & Wf & _).
destruct skelsN as (_ & _ & _ & _ & _ & AT87 & _ & SKf0 & _ & EFM1 & _).
assert (AG68 : env_agree 87 E' E8) by (apply env_agree_ewset).
assert (AG8 : env_agree 40 E00 E8) by (eapply env_agree_trans; [exact HA' | split; [intros kk Hk; apply (proj1 AG68); lia | exact (proj2 AG68)]]).
assert (E8_87 : ew E8 87 = Z_to_bv 64 fmhN) by (subst E8; apply ew_ewset_same).
assert (E8_40 : ew E8 40 = Z_to_bv 64 (ptr_addr L1 m)) by (rewrite <- E40'; apply (proj1 AG68); lia).
pose proof (key_rangeq m) as Rm. rewrite Eqm in Rm.
split; [| exact (conj AG68 (conj AG8 (conj E8_87 E8_40)))].
assert (HS0 : st_ok src0segs E8 ss_nf0 ms0) by (eapply (st_ok_agree src0segs 87 E' E8); [exact HS | exact AG68 | exact AT87]).
rewrite EFM1.
assert (HS1 : st_ok src0segs E8 (mkSS (ss_pc ss_nf0) (ss_regs ss_nf0) (R_fmh :: ss_mem ss_nf0) None (ss_facts ss_nf0)) ms0).
{ apply (st_ok_add_region src0segs E8 _ _ R_fmh HS0); [reflexivity | |].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_fmh ms_mem]; [lits; lia | lits; lia | |].
+ intros o Ho. rewrite Z.add_0_l. apply (proj1 (so_ctx_rw B (mid_syms _ _ _ _ _ MID) (ms_mem ms0) o ltac:(change (ms_ctx B) with CTX; unfold CTX_SIZE; lits; lia))).
+ apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_word src0segs E8 (ms_mem ms0) 0 (LOCK + 24) (SOff 87 0) fmhN); [apply den_off0; exact E8_87|].
rewrite Z.add_0_l. apply (word_mem_ext1 mm0); [| exact (Wf mm0 HM)].
intros kk Hk. apply F0; [lits; lia|]. unfold WDn0, WS. intros [Hw|Hw]; [lits; lia |]. destruct (Rm (LOCK + 24 + Z.of_nat kk) Kmq Hw) as [NI _]. apply NI. apply src0_rwseg_img. lits. lia.
- assert (DJm : LOCK + 32 <= ptr_addr L1 m \/ ptr_addr L1 m + 40 <= LOCK + 24).
{ destruct (Z_le_dec (ptr_addr L1 m + 40) (LOCK + 24)); [right; lia|]. left. destruct (Z_le_dec (LOCK + 32) (ptr_addr L1 m)); [lia|]. exfalso.
destruct (Z_lt_le_dec (ptr_addr L1 m) (LOCK + 24)).
- destruct (Rm (LOCK + 24) Kmq ltac:(lia)) as [NI' _]. apply NI'. apply src0_rwseg_img. lits. lia.
- destruct (Rm (ptr_addr L1 m) Kmq ltac:(lia)) as [NI _]. apply NI. apply src0_rwseg_img. lits. lia. }
assert (U40 : bv_unsigned (ew E8 40) = ptr_addr L1 m) by (rewrite E8_40; destruct (Rm (ptr_addr L1 m) Kmq ltac:(lia)) as (_ & R & _); apply u64_of_Z; lia).
apply Forall_forall. intros r Hr'. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr'. rewrite SKf0 in Hr'.
unfold extent_disjoint. cbn [r_base r_lo r_hi R_fmh base_val]. cbn [In] in Hr'.
destruct Hr' as [H|[H|[H|[H|[H|[H|[]]]]]]]; apply (f_equal (fun t => match t with (b, l, h) => (b, l, h) end)) in H; cbn in H; injection H as X1 X2 X3;
rewrite <- X1, <- X2, <- X3; cbn [base_val]; rewrite ?U40, ?(agree_reg' E8 2 AG8) by lia;
try replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : reg) by (apply bv_eq; reflexivity); fold sp; unfold ASF in *; lits; lia. }
apply (st_ok_add_fact src0segs E8 _ ms0 87 F_ptr0) in HS1. 2:{ unfold afact_ok, F_ptr0. cbn [af_lo af_hi af_al2]. rewrite E8_87, lit64_small by lia. change (2 ^ 3) with 8. repeat split; lia. }
exact HS1.
Qed.
Lemma station_NF2 : forall ms h0 rest hn mm0 ms2,
ring_ok (flinks (m :: X) sq) (st_free_meta_head sq) ms ->
(forall q, In q ms -> exists qp qn, MT sq q = Some (MFree qp qn) /\ memb q (m :: X) = false) ->
~ In m ms -> ms = h0 :: rest -> MT sq h0 = Some (MFree (Some (last ms m)) hn) ->
midrep B L' sq mm0 md' -> st_ok src0segs E8 ss_nf2 ms2 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ WDn1 x -> ms_mem ms2 (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x)) ->
let hp := last ms m in let E9 := ewset E8 88 (Z_to_bv 64 (ptr_addr L' hp)) in
st_ok src0segs E9 ss_NF2 ms2 /\ env_agree 88 E8 E9 /\ env_agree 40 E00 E9 /\
ew E9 88 = Z_to_bv 64 (ptr_addr L' hp) /\ ew E9 87 = Z_to_bv 64 (ptr_addr L' h0) /\ ew E9 40 = Z_to_bv 64 (ptr_addr L1 m) /\
In h0 (keys sq) /\ In hp (keys sq) /\ h0 <> m /\ hp <> m.
Proof.
intros ms h0 rest hn mm0 ms2 FRg MEMS Hmn Ems Mh0 HM HS F2 hp E9. pose proof (proj1 alloc_ceiling_val) as AC. destruct pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
pose proof sq_facts as (_ & MID' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Kmq & _ & Eqm & _ & HA' & E40').
pose proof fmhN_facts as (Hr & Hal & Wf & Hfm). destruct skelsN as (_ & _ & _ & _ & _ & _ & AT88 & _ & SKf2 & _ & EFM2).
assert (Ehd : st_free_meta_head sq = Some h0) by (destruct FRg as [_ HD]; rewrite HD, Ems; reflexivity).
destruct (Hfm h0 Ehd) as [Efmh Kh0].
assert (INlast : forall (l : list sptr) d, l <> [] -> In (last l d) l).
{ intros l. induction l as [|x t IHl]; intros d Hne; [exfalso; exact (Hne eq_refl)|]. destruct t as [|y t']; [left; reflexivity|]. right. apply IHl. discriminate. }
assert (Hhp : In hp ms) by (apply INlast; rewrite Ems; discriminate).
destruct (MEMS hp Hhp) as (lp & ln & Mhp & _). pose proof (In_keys_of_MT _ _ _ Mhp) as Khp.
assert (Hh0m : h0 <> m) by (intros ->; apply Hmn; rewrite Ems; left; reflexivity).
assert (Hhpm : hp <> m) by (intros Ehp; apply Hmn; rewrite <- Ehp; exact Hhp).
assert (E8_87 : ew E8 87 = Z_to_bv 64 (ptr_addr L' h0)) by (subst E8; rewrite ew_ewset_same, Efmh; reflexivity).
assert (E8_40 : ew E8 40 = Z_to_bv 64 (ptr_addr L1 m)) by (subst E8; rewrite ew_ewset_other by lia; exact E40').
assert (AG8 : env_agree 40 E00 E8) by (eapply env_agree_trans; [exact HA' | eapply env_agree_le; [| apply env_agree_ewset]; lia]).
assert (AG89 : env_agree 88 E8 E9) by (apply env_agree_ewset).
assert (AG9 : env_agree 40 E00 E9) by (eapply env_agree_trans; [exact AG8 | eapply env_agree_le; [| exact AG89]; lia]).
assert (E9_88 : ew E9 88 = Z_to_bv 64 (ptr_addr L' hp)) by (subst E9; apply ew_ewset_same).
assert (E9_87 : ew E9 87 = Z_to_bv 64 (ptr_addr L' h0)) by (rewrite <- E8_87; apply (proj1 AG89); lia).
assert (E9_40 : ew E9 40 = Z_to_bv 64 (ptr_addr L1 m)) by (rewrite <- E8_40; apply (proj1 AG89); lia).
pose proof (key_rangeq h0) as Rh0. pose proof (key_rangeq hp) as Rhp. pose proof (key_rangeq m) as Rm. rewrite Eqm in Rm.
destruct (Rh0 (ptr_addr L' h0) Kh0 ltac:(lia)) as (_ & Rh0a & _). destruct (Rh0 (ptr_addr L' h0 + 39) Kh0 ltac:(lia)) as (_ & Rh0b & _).
destruct (Rhp (ptr_addr L' hp) Khp ltac:(lia)) as (_ & Rhpa & _). destruct (Rhp (ptr_addr L' hp + 39) Khp ltac:(lia)) as (_ & Rhpb & _).
assert (U87 : bv_unsigned (ew E9 87) = ptr_addr L' h0) by (rewrite E9_87; apply lit64_small; lia).
assert (U88 : bv_unsigned (ew E9 88) = ptr_addr L' hp) by (rewrite E9_88; apply lit64_small; lia).
assert (ALp : ptr_addr L' hp mod 8 = 0) by exact (proj1 (proj2 (key_factsR (m :: X) None L' sq mem' md' hp HIq MID' Khp))).
pose proof (keys_apartq) as KA.
assert (OFF1 : forall q x, In q (keys sq) -> q <> m -> ptr_addr L' q <= x < ptr_addr L' q + 40 -> ~ WDn1 x).
{ intros q x Kq Hqm Hx Wx. destruct (key_rangeq q x Kq Hx) as (NI & Rx & _). unfold WDn1, WDn0, WS in Wx.
destruct Wx as [[Hw|Hw]|Hw]; [unfold ASF in *; lia | destruct (KA q m Kq Kmq Hqm); rewrite ?Eqm in *; lia | apply NI; apply src0_rwseg_img; lits; lia]. }
split; [| split; [exact AG89 | split; [exact AG9 | split; [exact E9_88 | split; [exact E9_87 | split; [exact E9_40 | split; [exact Kh0 | split; [exact Khp | exact (conj Hh0m Hhpm)]]]]]]]].
assert (HS0 : st_ok src0segs E9 ss_nf2 ms2) by (eapply (st_ok_agree src0segs 88 E8 E9); [exact HS | exact AG89 | exact AT88]).
rewrite EFM2.
assert (APART : forall lo hi r q, In q (keys sq) -> q <> m -> ptr_addr L' q <= lo -> hi <= ptr_addr L' q + 40 -> lo < hi -> In r (ss_mem ss_nf2) ->
hi <= base_val E9 (r_base r) + r_lo r \/ base_val E9 (r_base r) + r_hi r <= lo).
{ intros lo hi r q Kq Hqm Hlo Hhi Hlh Hr'. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr'. rewrite SKf2 in Hr'.
apply (apart_nf E9 lo hi r AG9 E9_40 Hlh); [| destruct (KA q m Kq Kmq Hqm); rewrite ?Eqm in *; lia | exact Hr'].
intros x Hx. destruct (key_rangeq q x Kq ltac:(lia)) as (NI & Rx & _). split; [exact NI | lia]. }
assert (HS1 : st_ok src0segs E9 (mkSS (ss_pc ss_nf2) (ss_regs ss_nf2) (R_hp :: ss_mem ss_nf2) None (ss_facts ss_nf2)) ms2).
{ apply (st_ok_add_region src0segs E9 _ _ R_hp HS0); [reflexivity | |].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_hp ms_mem]; rewrite U88; [lia | lia | | apply Forall_nil].
intros o Ho. apply present_writable. apply (present_keep mm0); [apply F2; [lia | apply (OFF1 hp _ Khp Hhpm); lia]|].
exact (key_presentq mm0 hp (ptr_addr L' hp + o) HM Khp ltac:(lia)).
- apply Forall_forall. intros r Hr'. unfold extent_disjoint. cbn [r_base r_lo r_hi R_hp base_val]. rewrite U88. exact (APART (ptr_addr L' hp + 8) (ptr_addr L' hp + 16) r hp Khp Hhpm ltac:(lia) ltac:(lia) ltac:(lia) Hr'). }
assert (HS2 : st_ok src0segs E9 (mkSS (ss_pc ss_nf2) (ss_regs ss_nf2) (R_hd :: R_hp :: ss_mem ss_nf2) None (ss_facts ss_nf2)) ms2).
{ apply (st_ok_add_region src0segs E9 _ _ R_hd HS1); [reflexivity | |].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_hd ms_mem]; rewrite U87; [lia | lia | |].
+ intros o Ho. apply present_writable. apply (present_keep mm0); [apply F2; [lia | apply (OFF1 h0 _ Kh0 Hh0m); lia]|].
exact (key_presentq mm0 h0 (ptr_addr L' h0 + o) HM Kh0 ltac:(lia)).
+ apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_word src0segs E9 (ms_mem ms2) (ptr_addr L' h0) 0 (SOff 88 0) (ptr_addr L' hp)); [apply den_off0; exact E9_88|].
apply (word_mem_ext1 mm0); [intros kk Hk; apply F2; [lia | apply (OFF1 h0 _ Kh0 Hh0m); lia]|].
replace (ptr_addr L' h0 + 0) with (ptr_addr L' (padd h0 META_prev)) by (rewrite ptr_addr_padd; unfold META_prev; lia).
change (ptr_addr L' hp) with (sval_num L' (VP hp)). apply (image_word L' sq mm0 md' _ _ HM); [| intros z; discriminate].
destruct (key_factsR (m :: X) None L' sq mem' md' h0 HIq MID' Kh0) as (_ & _ & CE & _).
apply CE. rewrite Mh0. cbn [meta_slot_cells optr]. left. reflexivity.
- apply Forall_cons.
+ unfold extent_disjoint. cbn [r_base r_lo r_hi R_hd R_hp base_val]. rewrite U87, U88.
destruct (sptr_eq_dec h0 hp) as [Ehh|Hne]; [rewrite Ehh; left; lia|]. destruct (KA h0 hp Kh0 Khp Hne); lia.
+ apply Forall_forall. intros r Hr'. unfold extent_disjoint. cbn [r_base r_lo r_hi R_hd base_val]. rewrite U87. exact (APART (ptr_addr L' h0 + 0) (ptr_addr L' h0 + 8) r h0 Kh0 Hh0m ltac:(lia) ltac:(lia) ltac:(lia) Hr'). }
apply (st_ok_add_fact src0segs E9 _ ms2 88 F_ptr0) in HS2. 2:{ unfold afact_ok, F_ptr0. cbn [af_lo af_hi af_al2]. rewrite U88. change (2 ^ 3) with 8. repeat split; lia. }
exact HS2.
Qed.
Lemma midrep_fmN : forall ms sf mm0 mem4 (W : Z -> Prop),
ring_ok (flinks (m :: X) sq) (st_free_meta_head sq) ms ->
(forall q, In q ms -> exists qp qn, MT sq q = Some (MFree qp qn) /\ memb q (m :: X) = false) ->
~ In m ms ->
(forall h0 rest, ms = h0 :: rest -> exists hn, MT sq h0 = Some (MFree (Some (last ms m)) hn)) ->
fm_post sq m ms sf ->
midrep B L' sq mm0 md' ->
(forall x, W x \/ ~ W x) ->
(forall x, 0 <= x < 2 ^ 64 -> ~ W x -> mem4 (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x)) ->
(forall x, W x -> WSn x \/ LOCK + 24 <= x < LOCK + 32 \/ ptr_addr L' m <= x < ptr_addr L' m + 16 \/
(ms <> [] /\ (ptr_addr L' (hd m ms) <= x < ptr_addr L' (hd m ms) + 8 \/ ptr_addr L' (last ms m) + 8 <= x < ptr_addr L' (last ms m) + 16))) ->
(forall x, ptr_addr L' m <= x < ptr_addr L' m + 16 -> present mem4 x) ->
(ms <> [] -> forall x, (ptr_addr L' (hd m ms) <= x < ptr_addr L' (hd m ms) + 8 \/ ptr_addr L' (last ms m) + 8 <= x < ptr_addr L' (last ms m) + 16) -> present mem4 x) ->
word_mem src0segs mem4 (LOCK + 24) (ptr_addr L' (hd m ms)) ->
word_mem src0segs mem4 (ptr_addr L' m) (ptr_addr L' (last ms m)) ->
word_mem src0segs mem4 (ptr_addr L' m + 8) (ptr_addr L' (hd m ms)) ->
(ms <> [] -> word_mem src0segs mem4 (ptr_addr L' (hd m ms)) (ptr_addr L' m) /\ word_mem src0segs mem4 (ptr_addr L' (last ms m) + 8) (ptr_addr L' m)) ->
midrep B L' sf mem4 md'.
Proof.
intros ms sf mm0 mem4 W FRg MEMS Hmn HD0 FP HM Wdec FR Wsub PRESm PRESh Wfmh Wm0 Wm8 Wring.
pose proof (proj1 alloc_ceiling_val) as AC. destruct pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
pose proof sq_facts as (_ & MID' & AMAq & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & XCq & Kmq & Mq & Eqm & _).
pose proof FP as (SB & EA & Hhd & MTm & MTo & MTr).
pose proof SB as (Sid & Smc & Sam & Samc & Saac & Ssh & Sah & Sat & Sama & Su & Suq & Sb & Ssq & Sbrk & Srg & Sar & Sk).
pose proof (mid_syms _ _ _ _ _ HM) as SO.
assert (Kms : forall q, In q ms -> In q (keys sq)) by (intros q Hq; destruct (MEMS q Hq) as (qp & qn & Mq' & _); exact (In_keys_of_MT _ _ _ Mq')).
assert (Kh0 : ms <> [] -> In (hd m ms) (keys sq)) by (intros Hne; apply Kms; destruct ms; [exfalso; exact (Hne eq_refl) | left; reflexivity]).
assert (INlast : forall (l : list sptr) d, l <> [] -> In (last l d) l).
{ intros l. induction l as [|x t IHl]; intros d Hne; [exfalso; exact (Hne eq_refl)|]. destruct t as [|y t']; [left; reflexivity|]. right. apply IHl. discriminate. }
assert (Khp : ms <> [] -> In (last ms m) (keys sq)) by (intros Hne; apply Kms; apply INlast; exact Hne).
assert (Hh0m : ms <> [] -> hd m ms <> m) by (intros Hne Eh; apply Hmn; rewrite <- Eh; destruct ms; [exfalso; exact (Hne eq_refl) | left; reflexivity]).
assert (Hhpm : ms <> [] -> last ms m <> m) by (intros Hne Eh; apply Hmn; rewrite <- Eh; apply INlast; exact Hne).
assert (CTXhi : CTX + CTX_SIZE <= alloc_ceiling) by exact (so_ctx_hi _ SO).
assert (Wlow : forall x, W x -> alloc_ceiling <= x \/ in_img B x \/ (exists q, In q (keys sq) /\ ptr_addr L' q <= x < ptr_addr L' q + 40 /\
(q = m /\ x < ptr_addr L' m + 16 \/ ms <> [] /\ (q = hd m ms /\ x < ptr_addr L' q + 8 \/ q = last ms m /\ ptr_addr L' q + 8 <= x < ptr_addr L' q + 16)))).
{ intros x Wx. destruct (Wsub x Wx) as [Hw|[Hw|[Hw|[Hne [Hw|Hw]]]]].
- left. unfold WS, ASF in *. lia.
- right. left. apply src0_rwseg_img. lits. lia.
- right. right. exists m. split; [exact Kmq|]. split; [lia|]. left. split; [reflexivity | lia].
- right. right. exists (hd m ms). split; [exact (Kh0 Hne)|]. split; [lia|]. right. split; [exact Hne|]. left. split; [reflexivity | lia].
- right. right. exists (last ms m). split; [exact (Khp Hne)|]. split; [lia|]. right. split; [exact Hne|]. right. split; [reflexivity | lia]. }
assert (UM : used_metas sf = used_metas sq).
{ apply used_metas_ext; [exact (proj1 (inv_keys HIq)) | exact Sk |]. intros q.
destruct (sptr_eq_dec q m) as [->|Hqm]; [right; rewrite MTm; destruct Mq as [Eq1|Eq1]; rewrite Eq1; split; reflexivity|].
destruct (In_dec sptr_eq_dec q ms) as [Hq|Hq].
- right. destruct (MEMS q Hq) as (qp & qn & Mq' & _). rewrite (MTr q _ Hq Mq'), Mq'. cbn. split; reflexivity.
- left. apply MTo. intros [Eq1|Eq1]; [exact (Hqm (eq_sym Eq1)) | exact (Hq Eq1)]. }
assert (RO : forall kk, region_of sf kk = region_of sq kk) by (intros kk; unfold region_of; rewrite Srg; reflexivity).
assert (MR' : memrep B L' sf mem4).
{ refine (memrep_xfer B (m :: X) None U L' L' sq sf mm0 mem4 md' HIq XCq AMAq HM UM [] _ _ _ _ _ eq_refl eq_refl _ W Wdec FR _
(m :: (match ms with [] => [] | _ => [hd m ms; last ms m] end)) _ _ _ _ _ _ _ _ _).
- rewrite app_nil_r. exact Sar.
- intros p q l H. discriminate.
- rewrite Sar. exact (proj1 (inv_areas HIq)).
- intros kk rg H Hl Hk. rewrite RO in H. exact H.
- intros kk rg H _ _. rewrite RO. exact H.
- intros; reflexivity.
- intros x kk rg Wx Hk Hl Hkd Hin. pose proof (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ HM) kk rg Hk Hl) as (_ & _ & Phi & Pimg).
destruct (Wlow x Wx) as [Hlo|[Hi|(q & Hq & Hqx & _)]]; [lia | exact (Pimg x Hin Hi) |].
destruct (key_nonmapq q x Hq Hqx) as [_ NM]. apply NM. exists kk, rg. split; [exact Hk|]. split; [exact Hl|]. split; [exact Hkd | exact Hin].
- intros x a Wx Ha Hax. left. destruct (areas_off_img B (m :: X) None U L' sq mm0 md' HIq HM a x Ha Hax) as [NI Rx].
destruct (Wlow x Wx) as [Hlo|[Hi|(q & Hq & Hqx & Hc)]]; [lia | exfalso; exact (NI Hi) |].
destruct Hc as [[-> Hx16]|[Hne [[-> Hx8]|[-> Hx8]]]].
+ exists m. split; [left; reflexivity | lia].
+ exists (hd m ms). split; [destruct ms; [exfalso; exact (Hne eq_refl) | right; left; reflexivity] | lia].
+ exists (last ms m). split; [destruct ms; [exfalso; exact (Hne eq_refl) | right; right; left; reflexivity] | lia].
- intros x a Wx Ha Hax. destruct (areas_off_img B (m :: X) None U L' sq mm0 md' HIq HM a x Ha Hax) as [NI Rx].
destruct (Wlow x Wx) as [Hlo|[Hi|(q & Hq & Hqx & Hc)]]; [lia | exfalso; exact (NI Hi) |].
destruct Hc as [[-> Hx16]|[Hne [[-> Hx8]|[-> Hx8]]]]; [apply PRESm; lia | apply (PRESh Hne); left; lia | apply (PRESh Hne); right; lia].
- intros q Hq. assert (Kq : In q (keys sq)).
{ destruct Hq as [<-|Hq]; [exact Kmq|]. destruct ms as [|h0 rest]; [destruct Hq|]. cbn [In] in Hq. destruct Hq as [<-|[<-|[]]]; [apply Kh0; discriminate | apply Khp; discriminate]. }
destruct (key_factsR (m :: X) None L' sq mem' md' q HIq MID' Kq) as (_ & _ & _ & (a & kk & Ha & Hk & Eq) & _). exists a, kk. auto.
- intros q Hq.
assert (OFFW : forall q' off, In q' (keys sq) -> q' <> m -> (ms <> [] -> q' = hd m ms -> 8 <= off) -> (ms <> [] -> q' = last ms m -> off + 8 <= 8) -> 0 <= off -> off + 8 <= 40 ->
forall jj, (jj < 8)%nat -> ~ W (ptr_addr L' q' + off + Z.of_nat jj)).
{ intros q' off Kq' Hq'm Hnh Hnl Ho1 Ho2 jj Hj Wx. destruct (key_rangeq q' (ptr_addr L' q' + off + Z.of_nat jj) Kq' ltac:(lia)) as (NI & Rx & _).
destruct (Wlow _ Wx) as [Hlo|[Hi|(q2 & Hq2 & Hq2x & Hc)]]; [lia | exact (NI Hi) |].
destruct (sptr_eq_dec q2 q') as [->|Hne2]; [| destruct (keys_apartq q2 q' Hq2 Kq' Hne2); lia].
destruct Hc as [[-> _]|[Hne [[-> Hx8]|[-> Hx8]]]]; [exact (Hq'm eq_refl) | pose proof (Hnh Hne eq_refl); lia | pose proof (Hnl Hne eq_refl); lia]. }
assert (OLD : forall q' off v, In q' (keys sq) -> q' <> m -> (ms <> [] -> q' = hd m ms -> 8 <= off) -> (ms <> [] -> q' = last ms m -> off + 8 <= 8) -> 0 <= off -> off + 8 <= 40 ->
In (MCell (LMem (padd q' off)) 8 v) (meta_slot_cells q' (MT sq q')) -> cell_mem B L' mem4 (MCell (LMem (padd q' off)) 8 v)).
{ intros q' off v Kq' H1 H2 H3 H4 H5 Hin.
destruct (key_factsR (m :: X) None L' sq mem' md' q' HIq MID' Kq') as (RB & _ & CE & _).
apply (YN2d.cell_mem_ext B L' mm0 mem4); [| exact (memrep_cell B L' sq mm0 _ (mid_mem _ _ _ _ _ HM) (CE _ Hin))].
cbn [mc_w mc_loc]. intros jj Hj. change (loc_addr L' (LMem (padd q' off))) with (ptr_addr L' (padd q' off)). rewrite ptr_addr_padd.
apply FR; [| exact (OFFW q' off Kq' H1 H2 H3 H4 H5 jj Hj)]. destruct (RB (ptr_addr L' q' + off + Z.of_nat jj) ltac:(unfold META_SIZE; lia)) as (_ & _ & R). lia. }
destruct Hq as [<-|Hq].
+ rewrite MTm. split; [destruct Mq as [Eq1|Eq1]; rewrite Eq1; exact I|]. split; [exact I|]. cbn [lnk_prev lnk_next optr].
split; [apply cell_of_word; rewrite Z.add_0_r; exact Wm0 | apply cell_of_word; exact Wm8].
+ destruct ms as [|h0 rest] eqn:Ems; [destruct Hq|]. rewrite <- Ems in *.
assert (Hne : ms <> []) by (rewrite Ems; discriminate).
assert (Eh0 : hd m ms = h0) by (rewrite Ems; reflexivity).
destruct (HD0 h0 rest Ems) as (hn & Mh0). destruct (Wring Hne) as [Wh0 Whp].
pose proof (INlast ms m Hne) as Hlast. destruct (MEMS _ Hlast) as (lp & ln & Mlast & _).
cbn [In] in Hq. destruct Hq as [<-|[<-|[]]].
* rewrite Eh0 in *. split; [rewrite Mh0; exact I|].
rewrite (MTr h0 _ ltac:(rewrite Ems; left; reflexivity) Mh0). rewrite sptr_eqb_refl. cbn [with_links lnk_prev lnk_next optr fst snd links_of nonused].
split; [exact I|]. split; [apply cell_of_word; rewrite Z.add_0_r; exact Wh0|].
destruct (sptr_eqb h0 (last ms m)) eqn:El.
-- apply sptr_eqb_eq in El. apply cell_of_word. rewrite El at 1. exact Whp.
-- apply sptr_eqb_neq in El. apply (OLD h0 8 (optr hn) (Kh0 Hne) (Hh0m Hne)); [intros; lia | intros _ El'; exfalso; exact (El El') | lia | lia |].
rewrite Mh0. cbn [meta_slot_cells]. right. left. reflexivity.
* split; [rewrite Mlast; exact I|].
rewrite (MTr _ _ Hlast Mlast). rewrite sptr_eqb_refl. rewrite Eh0. cbn [with_links lnk_prev lnk_next optr fst snd links_of nonused].
split; [exact I|]. split; [| apply cell_of_word; exact Whp].
destruct (sptr_eqb (last ms m) h0) eqn:El.
-- apply sptr_eqb_eq in El. apply cell_of_word. rewrite Z.add_0_r, El. rewrite Eh0 in Wh0. exact Wh0.
-- apply sptr_eqb_neq in El. apply (OLD (last ms m) 0 (optr lp) (Khp Hne) (Hhpm Hne)); [intros _ El'; exfalso; rewrite Eh0 in El'; exact (El El') | intros; lia | lia | lia |].
rewrite Mlast. cbn [meta_slot_cells]. left. reflexivity.
- intros a kk Ha Hk Hnin. set (q := slot_of a kk) in *.
assert (Hqm : q <> m) by (intros Eq1; apply Hnin; left; symmetry; exact Eq1).
destruct (In_dec sptr_eq_dec q ms) as [Hq|Hq]; [| apply MTo; intros [Eq1|Eq1]; [exact (Hqm (eq_sym Eq1)) | exact (Hq Eq1)]].
destruct (MEMS q Hq) as (qp & qn & Mq' & _). rewrite (MTr q _ Hq Mq'), Mq'.
assert (Hne : ms <> []) by (intros Eq1; rewrite Eq1 in Hq; exact Hq).
destruct (sptr_eqb q (hd m ms)) eqn:E1; [apply sptr_eqb_eq in E1; exfalso; apply Hnin; rewrite E1; destruct ms; [exfalso; exact (Hne eq_refl) | right; left; reflexivity]|].
destruct (sptr_eqb q (last ms m)) eqn:E2; [apply sptr_eqb_eq in E2; exfalso; apply Hnin; rewrite E2; destruct ms; [exfalso; exact (Hne eq_refl) | right; right; left; reflexivity]|].
reflexivity.
- intros p H. discriminate.
- intros p c H. discriminate.
- intros p x H. discriminate.
- intros c Hc. destruct (ctx_cells_fm sq sf c SB EA Hc) as [-> | (Hin & off & Hloc & Hoff & Hapart)].
+ right. rewrite Hhd. unfold cell_mem. cbn [mc_loc mc_w mc_val sval_num optr loc_addr]. rewrite (mid_ctx _ _ _ _ _ HM). change (ms_ctx B) with CTX.
replace (CTX + CTX_free_meta_head) with (LOCK + 24) by (unfold CTX_free_meta_head; lits; lia). exact Wfmh.
+ left. split; [exact Hin|]. intros kk Hk. rewrite Hloc. change (ms_ctx B) with CTX. intros Wx.
destruct (In_ctx_cells sq c Hin) as (off' & Hloc' & _ & Hsz). rewrite Hloc in Hloc'. injection Hloc' as <-.
destruct (Wlow _ Wx) as [Hlo|[Hi|(q & Hq & Hqx & _)]]; [unfold CTX_SIZE in *; lia | |].
* destruct (Wsub _ Wx) as [Hw|[Hw|[Hw|[Hne [Hw|Hw]]]]].
-- unfold WS, ASF, CTX_SIZE in *. lia.
-- unfold CTX_free_meta_head in Hapart. lits. lia.
-- destruct (key_rangeq m (CTX + off + Z.of_nat kk) Kmq ltac:(lia)) as (NI & _). apply NI. apply (so_ctx_img _ SO). change (ms_ctx B) with CTX. unfold CTX_SIZE in *. lia.
-- destruct (key_rangeq (hd m ms) (CTX + off + Z.of_nat kk) (Kh0 Hne) ltac:(lia)) as (NI & _). apply NI. apply (so_ctx_img _ SO). change (ms_ctx B) with CTX. unfold CTX_SIZE in *. lia.
-- destruct (key_rangeq (last ms m) (CTX + off + Z.of_nat kk) (Khp Hne) ltac:(lia)) as (NI & _). apply NI. apply (so_ctx_img _ SO). change (ms_ctx B) with CTX. unfold CTX_SIZE in *. lia.
* destruct (key_rangeq q (CTX + off + Z.of_nat kk) Hq Hqx) as (NI & _). apply NI. apply (so_ctx_img _ SO). change (ms_ctx B) with CTX. unfold CTX_SIZE in *. lia. }
pose proof (YN2i.ledger_same B L' sq md' (mid_ledger _ _ _ _ _ HM) (mid_ledgerx _ _ _ _ _ HM) sf md' Srg Sbrk eq_refl eq_refl eq_refl) as [LG2 LX2].
split.
- exact SO.
- exact MR'.
- eapply (tail_geom_xfer B (m :: X) None U L' L' sq sf mm0 md' HIq XCq HM); [exact UM | intros kk rg H _ _; rewrite RO; exact H | reflexivity | intros; reflexivity].
- apply (YN2d.statics_ok_ext B sq 0 mm0); [| exact (mid_statics _ _ _ _ _ HM)]. intros x Hx.
pose proof (so_img_hi _ SO x (so_statics_img _ SO x Hx)) as Hhi. apply FR; [lia|]. intros Wx.
destruct (Wlow _ Wx) as [Hlo|[Hi|(q & Hq & Hqx & _)]]; [lia | | destruct (key_rangeq q x Hq Hqx) as (NI & _); exact (NI (so_statics_img _ SO x Hx))].
destruct (Wsub _ Wx) as [Hw|[Hw|[Hw|[Hne [Hw|Hw]]]]].
+ unfold WS, ASF in *. lia.
+ apply (src0_SNC x Hx). change (ms_ctx B) with CTX. unfold CTX_SIZE. lits. lia.
+ destruct (key_rangeq m x Kmq ltac:(lia)) as (NI & _). exact (NI (so_statics_img _ SO x Hx)).
+ destruct (key_rangeq (hd m ms) x (Kh0 Hne) ltac:(lia)) as (NI & _). exact (NI (so_statics_img _ SO x Hx)).
+ destruct (key_rangeq (last ms m) x (Khp Hne) ltac:(lia)) as (NI & _). exact (NI (so_statics_img _ SO x Hx)).
- exact LG2.
- exact LX2.
- apply (YN2d.layout_ok_same L' sq sf (mid_layout _ _ _ _ _ HM) Srg). unfold footprint. rewrite Sar, Srg. f_equal. f_equal.
apply YN2c.flat_map_ext_in. intros kk _. rewrite RO. reflexivity.
- exact (mid_ctx _ _ _ _ _ HM).
- exact (mid_sec _ _ _ _ _ HM).
- exact (mid_md _ _ _ _ _ HM).
Qed.
Lemma finish_nf : forall Ef ssF ms4 sf i rstk ig,
st_ok src0segs Ef ssF ms4 -> finalS_check ssF (SLit (2 ^ 64 - 1)) = true -> env_agree 40 E00 Ef ->
nth_error (ss_mem ssF) i = Some rstk -> r_base rstk = Some 2%nat -> r_wlo rstk = - ASF -> r_whi rstk = 0 -> nth_error (ss_mem ssF) ig = Some R_guard ->
Inv X None U sf -> rawX X sf -> as_keep X A sf -> rsv_ok sf -> span_ok sf -> ama_ok sf -> bounded sf ->
st_regions sf = st_regions sq -> st_areas sf = st_areas sq -> used_metas sf = used_metas sq ->
midrep B L' sf (ms_mem ms4) md' ->
(forall x, 0 <= x < 2 ^ 64 -> ~ WSn x -> ~ (CTX <= x < CTX + CTX_SIZE) -> ~ (exists q, In q (keys sq) /\ ptr_addr L' q <= x < ptr_addr L' q + 40) ->
ms_mem ms4 (Z_to_bv 64 x) = mem' (Z_to_bv 64 x)) ->
SR src0segs (mkCfg ms4 md') (POSTn (-1, sf)).
Proof.
intros Ef ssF ms4 sf i rstk ig HS4 CK HAf Hi Hb Hwlo Hwhi Hig HI' RX' AKs RSVs SPOKs AMA' BND' Rs Ars UMs MID4 FR4.
pose proof (proj1 alloc_ceiling_val) as AC. destruct pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7). assert (EASF : ASF = 384) by reflexivity.
pose proof sq_facts as (LE' & MID' & AMAq & BNDq & RSVq & SPOKq & AK' & UB & HBel & VM' & FR' & SCR' & GD' & HAE & XCq & Kmq & Mq & Eqm & RXq & HA' & E40').
assert (XCs : Xclean X sf) by (intros x am Hx Hm'; destruct (RX' x Hx) as [EXR|EXR]; rewrite EXR in Hm'; discriminate).
destruct (finalS L A regs mem sc stk PRE g j1 j2 Ef ssF ms4 (SLit (2 ^ 64 - 1)) CK HS4 HAf) as (PRS & E1 & Hra & Hpc & Hrv & RA0).
apply (SR_final_retS Ef ssF ms4 md' _ HS4 Hrv Hpc Hra); [rewrite E1; exact P1 | exact Mhq | exact Mlzq |].
assert (RO : forall kk, region_of sf kk = region_of sq kk) by (intros kk; unfold region_of; rewrite Rs; reflexivity).
assert (FPe : footprint sf = footprint sq).
{ unfold footprint. rewrite Ars, Rs. f_equal. f_equal. apply YN2c.flat_map_ext_in. intros kk _. rewrite RO. reflexivity. }
assert (UBe : user_blocks sf = user_blocks sq) by (unfold user_blocks; rewrite UMs; reflexivity).
assert (OWe : forall x, owned B L' sf x <-> owned B L' sq x).
{ intros x. unfold owned, alloc_owned, in_footprint, in_user_block. rewrite FPe, UBe. tauto. }
assert (NMe : forall x, in_nonmap_region L' sf x <-> in_nonmap_region L' sq x).
{ intros x. unfold in_nonmap_region. split; intros [P Q]; (split; [destruct P as (r & rg & H); exists r, rg; rewrite ?RO in *; exact H | intros (r & rg & H); apply Q; exists r, rg; rewrite ?RO in *; exact H]). }
exists L', (ms_regs ms4), (ms_mem ms4), md'. cbn [fst snd].
split; [rewrite E1; reflexivity|]. split; [exact MID4|]. split; [exact AMA'|]. split; [exact BND'|]. split; [exact RSVs|]. split; [exact SPOKs|]. split.
{   destruct LE1 as (Y1 & Y2 & Y3 & Y4). destruct LE' as (Z1 & Z2 & Z3 & Z4). split; [congruence|]. split; [congruence|]. split; [congruence|].
intros r Hr. rewrite (Z4 r) by lia. exact (Y4 r Hr). }
split; [exact PRS|]. split; [exact VM'|]. split.
{ intros x Hx Nc No No' Nn Ns. unfold call_scratch, spZ in Ns. change (errno_addr B) with ERRNO in Ns. fold sp in Ns. change (ms_ctx B) with CTX in Nc.
assert (No2 : ~ owned B L' sq x) by (intros Ho; apply No'; apply (proj2 (OWe x)); exact Ho).
assert (Nn2 : ~ in_nonmap_region L' sq x) by (intros Hn'; apply Nn; apply (proj2 (NMe x)); exact Hn').
rewrite (FR4 x Hx); [| unfold WS; lia | exact Nc | intros (q & Kq & Hqx); apply Nn2; exact (key_nonmapq q x Kq Hqx)].
rewrite (FR' x Hx); [| lia | lia | exact Nc | | exact No2 | exact Nn2].
2:{ intros Ho. apply No2. exact (owned_mono (m :: X) (m :: X) None s1 sq L1 L' x HI1 XC1n HIq AK' UB LE' Ho). }
apply (FR1 x Hx); [unfold WS; lia | lia | exact Nc |].
intros Hn1. apply Nn2. exact (nonmap_keep (m :: X) (m :: X) None s1 sq L1 L' x HI1 XC1n HIq AK' UB LE' Hn1 No2). }
split.
{ intros a Ha. unfold call_scratch, spZ in Ha. change (errno_addr B) with ERRNO in Ha. fold sp in Ha.
destruct (Z_lt_le_dec a (sp - ASF)) as [Hlo|Hhi]; [| destruct Ha as [Ha|Ha]; [| lits; lia]].
- apply (writable_ext1 mem'); [apply FR4; [lits; lia | unfold WS; lits; lia | unfold CTX_SIZE; lits; lia |] | apply SCR'; lia].
intros (q & Kq & Hqx). destruct (key_rangeq q a Kq Hqx) as (NI & Ra & _). destruct Ha as [Ha|Ha]; [lia | apply NI; apply src0_rwseg_img; lits; lia].
- apply (writable_of_region regs Ef ssF ms4 i rstk a HS4 Hi). rewrite Hb, Hwlo, Hwhi. cbn [base_val]. rewrite (agree_reg' Ef 2 HAf ltac:(lia)).
replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : reg) by (apply bv_eq; reflexivity). fold sp. lia. }
split; [rewrite RA0; apply bv_eq; reflexivity|].
split; [intros H; lia|]. split; [exact AKs | exact (guard_of_state L A regs sc g j1 j2 Ef ssF ms4 ig HS4 HAf Hig)].
Qed.
Theorem leaf_nfree : forall ms0, st_ok src0segs E' ss_NRf ms0 -> ms_mem ms0 = mem' ->
mreal src0segs (mkCfg ms0 md') (ibind ((free_meta m ;; ret None) sq) KS) POSTn.
Proof.
intros ms0 HS0 Hmm0. pose proof (proj1 alloc_ceiling_val) as AC. destruct pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7). assert (EASF : ASF = 384) by reflexivity.
pose proof sq_facts as (LE' & MID' & AMAq & BNDq & RSVq & SPOKq & AK' & UB & HBel & VM' & FR' & SCR' & GD' & HAE & XCq & Kmq & Mq & Eqm & RXq & HA' & E40').
destruct fm_shapeN as (ms & sf & FRg & MEMS & Hmn & HD0 & Efm & FP & HI' & EU & RXs & AMAs & BNDs & Rs & Ars & AKs & RSVs & SPOKs & UMs).
pose proof fmhN_facts as (Hr & Hal & Wf & Hfm). destruct skelsN as (W0 & W1 & W2 & W3 & W4 & _).
pose proof finals_nfN as (CK1 & CK2 & (rs1 & Hrs1 & Hb1 & Hlo1 & Hhi1) & (rs2 & Hrs2 & Hb2 & Hlo2 & Hhi2) & G1 & G2 & Re0 & Re1 & Rn0 & Rn1 & Rn2 & Rn3).
assert (INlast : forall (l : list sptr) d, l <> [] -> In (last l d) l).
{ intros l. induction l as [|x t IHl]; intros d Hne; [exfalso; exact (Hne eq_refl)|]. destruct t as [|y t']; [left; reflexivity|]. right. apply IHl. discriminate. }
assert (Et : ibind ((free_meta m ;; ret None) sq) KS = IRet (-1, sf)) by (unfold bind at 1; rewrite Efm; reflexivity).
rewrite Et. cbn [mreal].
set (mm0 := ms_mem ms0) in *.
assert (HM0 : midrep B L' sq mm0 md') by (rewrite Hmm0; exact MID').
pose proof (key_rangeq m) as Rm. rewrite Eqm in Rm.
assert (RB : forall x, ptr_addr L1 m <= x < ptr_addr L1 m + 40 -> present mm0 x /\ ~ in_img B x /\ 4096 <= x < alloc_ceiling).
{ intros x Hx. destruct (key_factsR (m :: X) None L' sq mm0 md' m HIq HM0 Kmq) as (RB0 & _). rewrite Eqm in RB0. exact (RB0 x ltac:(unfold META_SIZE; lia)). }
destruct (RB (ptr_addr L1 m) ltac:(lia)) as (_ & _ & Rm0).
assert (ZB : forall i0, 0 <= i0 < 40 -> mbyte src0segs mm0 (ptr_addr L1 m + i0) = Some (Z_to_bv 8 0)).
{ intros i0 Hi0. rewrite <- Eqm. exact (mslot_zeroR (m :: X) None L' sq mm0 md' m HIq HM0 Kmq Mq i0 Hi0). }
assert (ZEROS : forall Ef ssF ms4 jj, st_ok src0segs Ef ssF ms4 -> ew Ef 40 = Z_to_bv 64 (ptr_addr L1 m) ->
nth_error (ss_mem ssF) jj = Some (YP09.mkRegion (Some 40%nat) 0 40 0 40 (firstn 2 (r_chunks (nth jj (ss_mem ssF) R_mslot)) ++ [mkChunk 16 (CVal 8 (SLit 0)); mkChunk 24 (CVal 8 (SLit 0)); mkChunk 32 (CVal 8 (SLit 0))])) ->
forall x, ptr_addr L1 m + 16 <= x < ptr_addr L1 m + 40 -> ms_mem ms4 (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x)).
{ intros Ef ssF ms4 jj HS4 Ef40 Hj x Hx.
assert (Uf : bv_unsigned (ew Ef 40) = ptr_addr L1 m) by (rewrite Ef40; destruct (RB (ptr_addr L1 m) ltac:(lia)) as (_ & _ & R); apply u64_of_Z; lia).
destruct (RB x ltac:(lia)) as (PR0 & NI & Rx).
rewrite (mbyte_present mm0 x (Z_to_bv 8 0)); [| replace x with (ptr_addr L1 m + (x - ptr_addr L1 m)) by lia; apply ZB; lia | exact PR0].
apply (mbyte_present (ms_mem ms4) x (Z_to_bv 8 0)).
- assert (CASE : exists off, In off [16; 24; 32] /\ ptr_addr L1 m + off <= x < ptr_addr L1 m + off + 8).
{ destruct (Z_lt_le_dec x (ptr_addr L1 m + 24)); [exists 16; split; [inlist | lia]|]. destruct (Z_lt_le_dec x (ptr_addr L1 m + 32)); [exists 24; split; [inlist | lia]|]. exists 32; split; [inlist | lia]. }
destruct CASE as (off & Hoff & Hxo). replace x with (bv_unsigned (ew Ef 40) + off + (x - ptr_addr L1 m - off)) by lia.
apply (zword_of_chunk_at regs Ef ssF ms4 jj _ 40 off HS4 Hj eq_refl); [| lia]. cbn [r_chunks]. apply in_app_iff. right.
cbn [In] in Hoff. destruct Hoff as [<-|[<-|[<-|[]]]]; inlist.
- apply (writable_off_img_present (ms_mem ms4) x ltac:(lia) ltac:(intros Hi; exact (NI (in_img1_img x Hi)))).
apply (writable_of_region regs Ef ssF ms4 jj _ x HS4 Hj). cbn [r_base r_wlo r_whi base_val]. rewrite Uf. lia. }
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E' ss_NRf ss_nf0); [exact Mhq | exact Mlzq | exact HS0 | apply run_NRf |].
intros ms1 HS1 Hfr1.
assert (F1 : forall x, 0 <= x < 2 ^ 64 -> ~ WDn0 x -> ms_mem ms1 (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x)).
{ apply (frame_keepN WDn0 E' (ss_mem ss_NRf) SKn0 mm0 _ mm0 Hfr1 W0); [intros b lo hi x Hin Hx; exact (SKn0_WDn0 E' b lo hi x HA' E40' Hin Hx) | intros; reflexivity]. }
destruct (station_NF1 ms1 mm0 HS1 HM0 F1) as (HS2 & AG68 & AG8 & E8_87 & E8_40).
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E8 ss_NF1 ss_nf1); [exact Mhq | exact Mlzq | exact HS2 | apply run_NF1 |].
intros ms3 HS3 Hfr3.
assert (F3 : forall x, 0 <= x < 2 ^ 64 -> ~ WDn1 x -> ms_mem ms3 (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x)).
{ apply (frame_keepN WDn1 E8 (ss_mem ss_NF1) SKn1 (ms_mem ms1) _ mm0 Hfr3 W1); [intros b lo hi x Hin Hx; exact (SKn1_WDn1 E8 b lo hi x AG8 E8_40 Hin Hx) |].
intros x Hx Hw. apply F1; [exact Hx | intros Hw0; apply Hw; left; exact Hw0]. }
assert (FRAME : forall (Wd : Z -> Prop) mmF, (forall x, 0 <= x < 2 ^ 64 -> ~ Wd x -> mmF (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x)) ->
(forall x, Wd x -> WSn x \/ LOCK + 24 <= x < LOCK + 32 \/ (exists q, In q (keys sq) /\ ptr_addr L' q <= x < ptr_addr L' q + 40)) ->
forall x, 0 <= x < 2 ^ 64 -> ~ WSn x -> ~ (CTX <= x < CTX + CTX_SIZE) -> ~ (exists q, In q (keys sq) /\ ptr_addr L' q <= x < ptr_addr L' q + 40) ->
mmF (Z_to_bv 64 x) = mem' (Z_to_bv 64 x)).
{ intros Wd mmF HFd HWd x Hx Nw Nc Nq. rewrite <- Hmm0. apply HFd; [exact Hx|]. intros Wx. destruct (HWd x Wx) as [Hw|[Hw|Hw]]; [exact (Nw Hw) | apply Nc; unfold CTX_SIZE; lits; lia | exact (Nq Hw)]. }
apply (SR_sym_branch src0segs E8 ss_nf1 ms3 md' _ BC_EQ (SOff 87 0) (SLit 0) HS3).
-
intros Hb HSb. rewrite (den_off0 E8 87 fmhN E8_87), den_lit, branch_eq, !lit64_small in Hb by lia. apply Z.eqb_eq in Hb.
assert (Ems : ms = []).
{ destruct FRg as [_ HD]. destruct ms as [|h0 rest]; [reflexivity|]. exfalso. cbn [hd_error] in HD. destruct (Hfm h0 HD) as [Efmh Kh0].
destruct (key_rangeq h0 (ptr_addr L' h0) Kh0 ltac:(lia)) as (_ & R0 & _). lia. }
subst ms. cbn [hd last] in *.
change (add_cond ss_nf1 (mkAC BC_EQ (SOff 87 0) (SLit 0))) with (add_cond ss_nf1 C_fe) in HSb.
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E8 (add_cond ss_nf1 C_fe) ss_nfeE); [exact Mhq | exact Mlzq | exact HSb | apply run_nfe |].
intros ms4 HS4 Hfr4.
assert (F4 : forall x, 0 <= x < 2 ^ 64 -> ~ WDn1 x -> ms_mem ms4 (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x)).
{ apply (frame_keepN WDn1 E8 (ss_mem (add_cond ss_nf1 C_fe)) SKn1 (ms_mem ms3) _ mm0 Hfr4 W2); [intros b lo hi x Hin Hx; exact (SKn1_WDn1 E8 b lo hi x AG8 E8_40 Hin Hx) | exact F3]. }
pose proof (ZEROS E8 ss_nfeE ms4 1%nat HS4 E8_40 ltac:(rewrite Re1; reflexivity)) as Z4.
set (W := fun x => WDn1 x /\ ~ (ptr_addr L1 m + 16 <= x < ptr_addr L1 m + 40)).
assert (HM4 : midrep B L' sf (ms_mem ms4) md').
{ apply (midrep_fmN [] sf mm0 (ms_mem ms4) W FRg MEMS Hmn HD0 FP HM0).
- intros x. subst W. unfold WDn1, WDn0, WS. lia.
- intros x Hx HW. destruct (Z_le_dec (ptr_addr L1 m + 16) x); [destruct (Z_lt_dec x (ptr_addr L1 m + 40)); [apply Z4; lia|]|]; (apply F4; [exact Hx | intros HW1; apply HW; split; [exact HW1 | lia]]).
- intros x [HW1 Hn16]. unfold WDn1, WDn0 in HW1. cbn [hd last]. rewrite Eqm. destruct HW1 as [[Hw|Hw]|Hw]; [left; exact Hw | right; right; left; lia | right; left; exact Hw].
- intros x Hx. rewrite Eqm in Hx. destruct (RB x ltac:(lia)) as (_ & NI & Rx). apply (writable_off_img_present _ x ltac:(lia) ltac:(intros Hi; exact (NI (in_img1_img x Hi)))).
apply (writable_of_region regs E8 ss_nfeE ms4 1 _ x HS4 Re1). cbn [r_base r_wlo r_whi base_val]. rewrite (proj1 AG68 40%nat), E40', u64_of_Z by lia. lia.
- intros H. exfalso. exact (H eq_refl).
- cbn [hd]. rewrite Eqm. apply (word_of_chunk regs E8 ss_nfeE ms4 0 _ (LOCK + 24) (SOff 40 0) _ HS4 Re0 eq_refl ltac:(left; reflexivity)). exact (den_off0 E8 40 _ E8_40).
- cbn [last]. rewrite Eqm. replace (ptr_addr L1 m) with (bv_unsigned (ew E8 40) + 0) at 1 by (rewrite E8_40, u64_of_Z by lia; lia).
apply (word_of_chunk_at E8 ss_nfeE ms4 1 _ 40 0 (SOff 40 0) _ HS4 Re1 eq_refl ltac:(right; left; reflexivity)). exact (den_off0 E8 40 _ E8_40).
- cbn [hd]. rewrite Eqm. replace (ptr_addr L1 m + 8) with (bv_unsigned (ew E8 40) + 8) by (rewrite E8_40, u64_of_Z by lia; lia).
apply (word_of_chunk_at E8 ss_nfeE ms4 1 _ 40 8 (SOff 40 0) _ HS4 Re1 eq_refl ltac:(left; reflexivity)). exact (den_off0 E8 40 _ E8_40).
- intros H. exfalso. exact (H eq_refl). }
apply (finish_nf E8 ss_nfeE ms4 sf 2%nat rs1 4%nat HS4 CK1 AG8 Hrs1 Hb1 Hlo1 Hhi1 G1 HI' RXs AKs RSVs SPOKs AMAs BNDs Rs Ars UMs HM4).
apply (FRAME WDn1 _ F4). intros x Hw. unfold WDn1, WDn0 in Hw. destruct Hw as [[Hw|Hw]|Hw]; [left; exact Hw | right; right; exists m; rewrite Eqm; exact (conj Kmq Hw) | right; left; exact Hw].
-
intros Hb HSb. rewrite (den_off0 E8 87 fmhN E8_87), den_lit, branch_eq, !lit64_small in Hb by lia. apply Z.eqb_neq in Hb.
destruct ms as [|h0 rest] eqn:Ems; [exfalso; apply Hb; unfold fmhN; destruct FRg as [_ HD]; rewrite HD; reflexivity|]. rewrite <- Ems in *.
assert (Hne : ms <> []) by (rewrite Ems; discriminate).
destruct (HD0 h0 rest Ems) as (hn & Mh0).
change (add_cond ss_nf1 (mkAC (neg_bc BC_EQ) (SOff 87 0) (SLit 0))) with (add_cond ss_nf1 C_fne) in HSb.
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E8 (add_cond ss_nf1 C_fne) ss_nf2); [exact Mhq | exact Mlzq | exact HSb | apply run_nfne |].
intros ms4 HS4 Hfr4.
assert (F4 : forall x, 0 <= x < 2 ^ 64 -> ~ WDn1 x -> ms_mem ms4 (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x)).
{ apply (frame_keepN WDn1 E8 (ss_mem (add_cond ss_nf1 C_fne)) SKn1 (ms_mem ms3) _ mm0 Hfr4 W3); [intros b lo hi x Hin Hx; exact (SKn1_WDn1 E8 b lo hi x AG8 E8_40 Hin Hx) | exact F3]. }
destruct (station_NF2 ms h0 rest hn mm0 ms4 FRg MEMS Hmn Ems Mh0 HM0 HS4 F4) as (HS5 & AG89 & AG9 & E9_88 & E9_87 & E9_40 & Kh0 & Khp & Hh0m & Hhpm).
set (hp := last ms m) in *. set (E9 := ewset E8 88 (Z_to_bv 64 (ptr_addr L' hp))) in *.
assert (Eh0 : hd m ms = h0) by (rewrite Ems; reflexivity).
destruct (key_rangeq h0 (ptr_addr L' h0) Kh0 ltac:(lia)) as (_ & Rh0a & _). destruct (key_rangeq h0 (ptr_addr L' h0 + 39) Kh0 ltac:(lia)) as (_ & Rh0b & _).
destruct (key_rangeq hp (ptr_addr L' hp) Khp ltac:(lia)) as (_ & Rhpa & _). destruct (key_rangeq hp (ptr_addr L' hp + 39) Khp ltac:(lia)) as (_ & Rhpb & _).
assert (U87 : bv_unsigned (ew E9 87) = ptr_addr L' h0) by (rewrite E9_87; apply lit64_small; lia).
assert (U88 : bv_unsigned (ew E9 88) = ptr_addr L' hp) by (rewrite E9_88; apply lit64_small; lia).
assert (U40' : bv_unsigned (ew E9 40) = ptr_addr L1 m) by (rewrite E9_40; destruct (RB (ptr_addr L1 m) ltac:(lia)) as (_ & _ & R); apply u64_of_Z; lia).
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E9 ss_NF2 ss_nfneE); [exact Mhq | exact Mlzq | exact HS5 | apply run_NF2 |].
intros ms5 HS6 Hfr5.
assert (F5 : forall x, 0 <= x < 2 ^ 64 -> ~ WDn2 (ptr_addr L' h0) (ptr_addr L' hp) x -> ms_mem ms5 (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x)).
{ apply (frame_keepN (WDn2 (ptr_addr L' h0) (ptr_addr L' hp)) E9 (ss_mem ss_NF2) SKn2 (ms_mem ms4) _ mm0 Hfr5 W4); [intros b lo hi x Hin Hx; exact (SKn2_WDn2 E9 b lo hi x _ _ AG9 E9_40 U87 U88 Hin Hx) |].
intros x Hx Hw. apply F4; [exact Hx | intros Hw1; apply Hw; left; exact Hw1]. }
pose proof (ZEROS E9 ss_nfneE ms5 3%nat HS6 E9_40 ltac:(rewrite Rn3; reflexivity)) as Z5.
set (W := fun x => WDn2 (ptr_addr L' h0) (ptr_addr L' hp) x /\ ~ (ptr_addr L1 m + 16 <= x < ptr_addr L1 m + 40)).
assert (HM5 : midrep B L' sf (ms_mem ms5) md').
{ apply (midrep_fmN ms sf mm0 (ms_mem ms5) W FRg MEMS Hmn HD0 FP HM0).
- intros x. subst W. unfold WDn2, WDn1, WDn0, WS. lia.
- intros x Hx HW. destruct (Z_le_dec (ptr_addr L1 m + 16) x); [destruct (Z_lt_dec x (ptr_addr L1 m + 40)); [apply Z5; lia|]|]; (apply F5; [exact Hx | intros HW1; apply HW; split; [exact HW1 | lia]]).
- intros x [HW1 Hn16]. unfold WDn2, WDn1, WDn0 in HW1. rewrite Eh0, Eqm.
destruct HW1 as [[[Hw|Hw]|Hw]|[Hw|Hw]]; [left; exact Hw | right; right; left; lia | right; left; exact Hw | right; right; right; split; [exact Hne | left; exact Hw] | right; right; right; split; [exact Hne | right; exact Hw]].
- intros x Hx. rewrite Eqm in Hx. destruct (RB x ltac:(lia)) as (_ & NI & Rx). apply (writable_off_img_present _ x ltac:(lia) ltac:(intros Hi; exact (NI (in_img1_img x Hi)))).
apply (writable_of_region regs E9 ss_nfneE ms5 3 _ x HS6 Rn3). cbn [r_base r_wlo r_whi base_val]. rewrite U40'. lia.
- intros _ x Hx. rewrite Eh0 in Hx. fold hp in Hx.
assert (NI : ~ in_img1 x) by (intros Hi; apply in_img1_img in Hi; destruct Hx as [Hx|Hx]; [exact (proj1 (key_rangeq h0 x Kh0 ltac:(lia)) Hi) | exact (proj1 (key_rangeq hp x Khp ltac:(lia)) Hi)]).
apply (writable_off_img_present _ x ltac:(lia) NI). destruct Hx as [Hx|Hx].
+ apply (writable_of_region regs E9 ss_nfneE ms5 0 _ x HS6 Rn0). cbn [r_base r_wlo r_whi base_val]. rewrite U87. lia.
+ apply (writable_of_region regs E9 ss_nfneE ms5 1 _ x HS6 Rn1). cbn [r_base r_wlo r_whi base_val]. rewrite U88. lia.
- rewrite Eh0. apply (word_of_chunk regs E9 ss_nfneE ms5 2 _ (LOCK + 24) (SOff 87 0) _ HS6 Rn2 eq_refl ltac:(left; reflexivity)). exact (den_off0 E9 87 _ E9_87).
- rewrite Eqm. replace (ptr_addr L1 m) with (bv_unsigned (ew E9 40) + 0) at 1 by lia. apply (word_of_chunk_at E9 ss_nfneE ms5 3 _ 40 0 (SOff 88 0) _ HS6 Rn3 eq_refl ltac:(left; reflexivity)). exact (den_off0 E9 88 _ E9_88).
- rewrite Eh0, Eqm. replace (ptr_addr L1 m + 8) with (bv_unsigned (ew E9 40) + 8) by lia. apply (word_of_chunk_at E9 ss_nfneE ms5 3 _ 40 8 (SOff 87 0) _ HS6 Rn3 eq_refl ltac:(right; left; reflexivity)). exact (den_off0 E9 87 _ E9_87).
- intros _. rewrite Eh0, Eqm. split.
+ replace (ptr_addr L' h0) with (bv_unsigned (ew E9 87) + 0) at 1 by lia. apply (word_of_chunk_at E9 ss_nfneE ms5 0 _ 87 0 (SOff 40 0) _ HS6 Rn0 eq_refl ltac:(left; reflexivity)). exact (den_off0 E9 40 _ E9_40).
+ fold hp. replace (ptr_addr L' hp + 8) with (bv_unsigned (ew E9 88) + 8) by lia. apply (word_of_chunk_at E9 ss_nfneE ms5 1 _ 88 8 (SOff 40 0) _ HS6 Rn1 eq_refl ltac:(left; reflexivity)). exact (den_off0 E9 40 _ E9_40). }
apply (finish_nf E9 ss_nfneE ms5 sf 4%nat rs2 6%nat HS6 CK2 AG9 Hrs2 Hb2 Hlo2 Hhi2 G2 HI' RXs AKs RSVs SPOKs AMAs BNDs Rs Ars UMs HM5).
apply (FRAME (WDn2 (ptr_addr L' h0) (ptr_addr L' hp)) _ F5). intros x Hw. unfold WDn2, WDn1, WDn0 in Hw.
destruct Hw as [[[Hw|Hw]|Hw]|[Hw|Hw]]; [left; exact Hw | right; right; exists m; rewrite Eqm; exact (conj Kmq Hw) | right; left; exact Hw | |].
+ right; right. exists h0. split; [exact Kh0 | lia].
+ right; right. exists hp. split; [exact Khp | lia].
Qed.
End NB.
Definition NSUCC : Prop := forall r c', 0 <= fst r -> NRpost r c' -> mreal src0segs c' (ibind (nest_rest sc m K j (fst r) (snd r)) KS) POSTn.
Theorem nest_from_parts : NSUCC -> forall ms, st_ok src0segs E (add_cond ss_g4 C_nest) ms -> FRM1n (ms_mem ms) ->
mreal src0segs (mkCfg ms md1) (ibind (nest_body fuel sc n m s1) KS) POSTn.
Proof.
intros SUCC ms HS HF. pose proof facts_N as (HK & Hj & J3 & Hcs & Hfit & Hk & Etot & H23 & Hscj & NN & Hj48 & HKr & Hnu).
pose proof (nest_body_eq fuel sc n m s1) as NB. cbv zeta in NB. fold K in NB. rewrite <- Etot in NB. rewrite Hj in NB. rewrite NB, ibind_assoc.
eapply mreal_SR_pre; [exact (reach_NC ms HS HF)|]. intros c1 H1.
apply (mreal_ibind src0segs (alloc_slot fuel j total s1) (fun r => ibind (KN sc m K j r) KS) c1 NRpost POSTn (call_nest c1 H1)).
intros r c' NR. unfold KN. destruct (fst r <? 0) eqn:Eneg.
- apply Z.ltb_lt in Eneg. destruct NR as (L' & mem' & md' & E' & Ec & BASE & [[Hm1 [HI' HS']] | [Hge _]]); [| lia].
rewrite Ec. apply (leaf_nfree (snd r) L' mem' md' E' BASE HI'); [| reflexivity]. rewrite Ec in HS'. exact HS'.
- apply Z.ltb_ge in Eneg. exact (SUCC r c' Eneg NR).
Qed.
End NA.
Definition NSUCC_all : Prop := forall m s1 L1 mem1 md1 E,
Inv (m :: X) None U s1 -> rawX X s1 -> as_keep X A s1 -> (MT s1 m = Some MRaw \/ MT s1 m = Some (MFree None None)) -> In m (keys s1) -> memb m X = false ->
(forall g' am, usedX (m :: X) s1 g' am <-> usedX X A g' am) -> st_active s1 = st_active A -> (length (st_regions A) <= length (st_regions s1))%nat ->
layout_le A L L1 -> midrep B L1 s1 mem1 md1 -> ama_ok s1 -> bounded s1 -> (exists vm', md1 = with_vmmaps vm' md) ->
(forall x, 0 <= x < 2 ^ 64 -> ~ WSn x -> ~ (ERRNO <= x < ERRNO + 4) -> ~ (CTX <= x < CTX + CTX_SIZE) -> ~ in_nonmap_region L1 s1 x -> mem1 (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
(forall a, ERRNO <= a < ERRNO + 4 -> writable_at src0segs mem1 a) ->
env_agree 40 E00 E -> ew E 40 = Z_to_bv 64 (ptr_addr L1 m) ->
ew E 56 = Z_to_bv 64 (usage_of s1 sc) -> ew E 61 = Z_to_bv 64 (initial_cnt sc (usage_of s1 sc)) ->
ew E 62 = Z_to_bv 64 (16 * nu * initial_cnt sc (usage_of s1 sc)) -> class_size sc * initial_cnt sc (usage_of s1 sc) + UNIT <= PGSZ / 2 ->
NSUCC m s1 L1 mem1 E.
Theorem nest_at_from_succ : NSUCC_all -> SEG_nest_at X U L A regs mem md sc n stk g j1 j2 fuel.
Proof.
intros SUCC m s1 L1 mem1 md1 c AF G4 Harm.
destruct AF as ([Q [RX1 AK1]] & LE1 & MID1 & AMA1 & BND1 & VM1 & FR1 & ERRW1).
destruct Q as (AFR & UBS & HI1 & NXm & Km & Mm & US1). cbn [fst snd] in AFR, UBS, HI1, NXm, Km, Mm, US1.
destruct AFR as (ACT1 & USG1 & RG1 & LEN1 & MC1).
pose proof G4 as (E & ms & Ec & HS & HA' & E40 & E56 & E61 & E62 & HF). subst c.
apply (nest_from_parts m s1 L1 mem1 md1 HI1 RX1 AK1 Mm Km NXm US1 LEN1 LE1 MID1 AMA1 BND1 VM1 FR1 ERRW1 E HA' E40 E62 Harm).
- apply (SUCC m s1 L1 mem1 md1 E); first [assumption | exact ACT1 | exact E56 | exact E61].
- exact HS.
- exact HF.
Qed.
End s.
Definition NEST_SUCC : Prop :=
forall X U L A regs mem md sc n stk g j1 j2 fuel,
Inv X None U A -> rawX X A -> ama_ok A -> bounded A -> rsv_ok A -> span_ok A -> 0 <= sc < 48 -> 0 <= n < MMAP_THRESHOLD ->
midrep B L A mem md -> (st_init_done A = false -> auxv_pre B (ly_sec L) (spZ regs) mem) -> callee_pre B regs mem stk -> ASF <= stk <= AS_STACK ->
getr regs 10 = Z_to_bv 64 sc -> getr regs 11 = Z_to_bv 64 n -> word_mem src0segs mem GUARD g ->
(forall k, U k = 0) -> as_budget sc <= stk -> (need sc <= S (S fuel))%nat -> ASH fuel ->
NSUCC_all X U L A regs mem md sc stk g j1 j2.
Theorem src0_SEG_nest_partial : alloc_meta_hyp B -> NEST_SUCC -> SEG_nest.
Proof.
intros AMH SUCC fuel IH X U L A regs mem md sc n stk g j1 j2 HI RX AMA BND RSV SPOK Hsc Hn MID AUXP PRE Hstk R10 R11 Hg HU HB HN.
apply (nest_at_from_succ X U L A regs mem md sc n stk HI RX RSV SPOK Hsc Hn MID PRE Hstk g j1 j2 HU HB fuel HN IH).
exact (SUCC X U L A regs mem md sc n stk g j1 j2 fuel HI RX AMA BND RSV SPOK Hsc Hn MID AUXP PRE Hstk R10 R11 Hg HU HB HN IH).
Qed.
Corollary src0_alloc_slot_partial4 : alloc_meta_hyp B -> (forall fuel, SEG_group_at fuel -> SEG_head_at fuel) -> NEST_SUCC -> alloc_slot_hyp B.
Proof. intros AMH SH SU. exact (src0_alloc_slot_partial3 AMH SH (src0_SEG_nest_partial AMH SU)). Qed.
End e.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
