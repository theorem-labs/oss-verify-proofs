(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; every address measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6, same loaded bytes): the block lemma w6b_c4 of
   lib/A/RPgW6bBase.v, case 4 of ent_build's `switch (kind % 10)` (pod.h:326-331) inside LLVMFuzzerTestOneInput,
   from the case entry 0x80e68 to the join J 0x8165c. Proves no function (kind: segment lemma).

   THE CODE (registers as in RPgW6aBase.v: s1 = R, s7 = SHADOW_OFF, s8 = c the cursor, s9 = what is left, a4 = c - 1):
     0x80e68  beqz s9 -> 0x811c8                   no byte is left: v = 0 and nothing is read
     0x80e6c .. 0x80e7c  the instrumented check of s8 (a load of the shadow byte and a compare; its slow block is
                         0x819d8), with `ld s4,0xb0(s1)` between the load and the branch
     0x80e80  lbu a0,0(s8) (= v); a1 := [R+0xf8] - 2; sd a1,0xf8(s1); s8 := a4 + 2
     0x80e94 .. 0x80eb0  a0 := (v - ((v * 0xab) >> 9) - 2 * ((v * 0xab) >> 9)) & 0xff, which is v mod 3 for every one
                         of the 256 bytes (pod.h:327); j 0x811d4
     0x811c8  sd zero,0xf8(s1); a0 := 0; ld s4,0xb0(s1)
     0x811d4  a1 := [R+0xf0] (= the address of e); sw 2,0(a1) (e.type = POD_BOOL); sw 4,4(a1) (e.size = 4);
              sw a0,8(a1) (e.body[0..4) = v mod 3); j 0x81658
     0x81658  mv s9,s8                                                                     -> J 0x8165c
   The three stores into e ask no obligation: e is in scope at the case entry (its 13 shadow granules are 0) and the
   shadow entry of lib/A/RPgEntBKit.v covers it. The one obligation the run leaves is the input read's, paid from
   the piece's range_addressable over the input bytes.
   THE PROOF: the entry state of lib/A/RPgEntBKit.v (eb_entry), the branch on s9 split by srr_branch_tok, one engine
   run per arm to J, and the post read off the run's final state: the registers from their symbolic values, e's 104
   bytes from the three stored chunks and the 92 bytes of the zero chunk that is left, [R+0xf8] from the cell of the
   region over [R+0xf0, R+0x100), every byte outside w6b_wr from the run's frame. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgSteps RPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgW6aBase RPgW6aC2h RPgW6aTail RPgEntBKit RPgW6bBase.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgCfgChanges.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ======================================== the model ======================================== *)
(* ent_build of a turn whose kind byte is 4 mod 10 (pod.h:326-331) *)
Lemma c4_model : forall (bb : byte) (l : list byte), bv_unsigned bb mod 10 = 4 ->
  ent_build (bb :: l) = (Ent POD_BOOL 4 (le32 (fst (fuzz_u8 l) mod 3)), snd (fuzz_u8 l)).
Proof.
intros bb l H. unfold ent_build. cbn [fuzz_u8]. rewrite H. cbn [Z.to_nat].
destruct (fuzz_u8 l) as [v l1] eqn:E. cbn [fst snd]. reflexivity.
Qed.

(* ======================================== the arithmetic ======================================== *)
(* a0 at 0x811e8 as the engine computes it from the input byte (atom 35): the mul-shift remainder of pod.h:327,
   checked for all 256 bytes *)
Definition c4_a0 : sv :=
SAlu ALU_AND
  (SAlu ALU_SUB
     (SAlu ALU_SUB (SExt false 8 (SOff 35 0))
        (SAlu ALU_SRL (SMd M_MUL (SExt false 8 (SOff 35 0)) (SLit 171)) (SLit 9)))
     (SAlu ALU_SLL (SAlu ALU_SRL (SMd M_MUL (SExt false 8 (SOff 35 0)) (SLit 171)) (SLit 9)) (SLit 1)))
  (SLit 255).
Lemma c4_a0_val : forall E m, ew E 35 = Z_to_bv 64 m -> 0 <= m < 256 ->
  sv_denot E c4_a0 = Z_to_bv 64 (m mod 3).
Proof.
intros E m Hm Hr.
transitivity (sv_denot (c2_envz m) c4_a0); [unfold c4_a0; cbn [sv_denot ew c2_envz]; rewrite Hm; reflexivity|].
apply bv_eq. apply Z.eqb_eq.
exact (c2_all256 (fun m => bv_unsigned (sv_denot (c2_envz m) c4_a0) =? bv_unsigned (Z_to_bv 64 (m mod 3)))
  ltac:(vm_compute; reflexivity) m Hr).
Qed.

(* a chunk of a region of a final state, by its place in the chunk list *)
Ltac c4_in := cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ======================================== reading the final state ======================================== *)
(* the kernel's byte list of the statement is RPgMem's rm_bytes of the model's byte list *)
Lemma c4_garr : forall (H : word -> bool) mem a l, rm_bytes rsegs H mem a l ->
  garr8 rsegs (mrestrict H mem) a (map (fun x : byte => bv_unsigned x) l).
Proof. intros H mem a l Hb. exact Hb. Qed.

(* a zero chunk of a region of a final state *)
Lemma c4_zero_at : forall E ss (H : word -> bool) ms i rg off len a j,
st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some rg ->
In (YP09.mkChunk off (CZero len)) (YP09.r_chunks rg) ->
a = base_val E (YP09.r_base rg) + off -> 0 <= j < len ->
mbyte rsegs (mrestrict H (ms_mem ms)) (a + j) = Some (Z_to_bv 8 0).
Proof.
intros E ss H ms i rg off len a j HS Hi Hc -> Hj.
exact (eb_chunk_zero E (mrestrict H (ms_mem ms)) rg off len
  (eb_region E ss (restrict H ms) rg HS (nth_error_In _ _ Hi)) Hc j Hj).
Qed.

(* one 4-byte field of e, then the rest of the list *)
Lemma c4_app4 : forall (H : word -> bool) mem a v (l : list byte),
val_mem rsegs (mrestrict H mem) a 4 v -> rm_bytes rsegs H mem (a + 4) l ->
rm_bytes rsegs H mem a (Z_to_le_bytes 4 v ++ l).
Proof.
intros H mem a v l Hv Hl. apply rm_bytes_app. split; [apply rm_bytes_of_val; exact Hv|].
rewrite length_Z_to_le_bytes. change (Z.of_nat 4) with 4. exact Hl.
Qed.

(* e's 104 bytes: the three stored words and the 92 bytes of the zero chunk that is left *)
Lemma c4_e_image : forall (H : word -> bool) mem a v,
val_mem rsegs (mrestrict H mem) a 4 2 ->
val_mem rsegs (mrestrict H mem) (a + 4) 4 4 ->
val_mem rsegs (mrestrict H mem) (a + 8) 4 v ->
(forall i, 0 <= i < 92 -> mbyte rsegs (mrestrict H mem) (a + 12 + i) = Some (Z_to_bv 8 0)) ->
garr8 rsegs (mrestrict H mem) a (map (fun x : byte => bv_unsigned x) (ent_mem (Ent POD_BOOL 4 (le32 v)))).
Proof.
intros H mem a v V0 V4 V8 Vz. apply c4_garr.
unfold ent_mem. cbn [e_type e_size e_body]. rewrite length_le32.
replace (le32 POD_BOOL ++ le32 4 ++ le32 v ++ zeros (96 - 4))
  with (Z_to_le_bytes 4 2 ++ Z_to_le_bytes 4 4 ++ Z_to_le_bytes 4 v ++ repeat (Z_to_bv 8 0) 92) by reflexivity.
apply c4_app4; [exact V0|].
apply c4_app4; [exact V4|].
replace (a + 4 + 4) with (a + 8) by lia.
apply c4_app4; [exact V8|].
replace (a + 8 + 4) with (a + 12) by lia.
apply rm_bytes_aview. intros i Hi. rewrite rm_length_repeat in Hi.
rewrite (rm_nth_repeat (Z_to_bv 8 0) (Z_to_bv 8 0) 92 i Hi).
unfold aview. rewrite (Vz (Z.of_nat i) ltac:(lia)). reflexivity.
Qed.

(* every byte outside the run's write windows is kept *)
Lemma c4_keep : forall (W : world rsegs) E (rs : smem) (m0 m1 : word -> option byte) (R F : Z),
frame_of E rs (mrestrict (w_H W) m0) (mrestrict (w_H W) m1) ->
(forall rg, In rg rs -> forall a, base_val E (YP09.r_base rg) + YP09.r_wlo rg <= a <
   base_val E (YP09.r_base rg) + YP09.r_whi rg -> w6b_wr R F a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ w6b_wr R F a -> aview rsegs (w_H W) m1 a = aview rsegs (w_H W) m0 a.
Proof.
intros W E rs m0 m1 R F HFr Hwr a Ha Hn. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
intros (rg & Hin & Hr). rewrite unsigned_lit_small in Hr by lia. exact (Hn (Hwr rg Hin a Hr)).
Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* ======================================== the block lemma ======================================== *)
Theorem w6b_c4 : w6b_c4_stmt B MT.
Proof using MTL LAWS.
unfold w6b_c4_stmt, w6b_case_stmt. cbv beta.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c vb pp b r Hctx Hkd Hin _.
destruct Hctx as (HJ & HR16 & HRsp & HspR & Hown & HF & Hrom).
destruct Hin as (H2 & H3 & H4 & H9 & H23 & H24 & H14 & H25 & H21 & H27 & H20 & Vf8 & Vb0 & Vf0 & Vc0 & V20 & V70 & V80
  & Hvb & Hkdr & Hpp1 & Hpp2 & HFa & HFb & HF32 & Hez & Hera & Hehull & Hc1 & Hwin & Hinhull & Hdis).
destruct Hwin as (Hg & Hrain & Hc0 & Hcle & Ham & Hdisw).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
destruct Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (Hac & _).
pose proof RPgCfgChanges.cfg_wx as Hwx. pose proof RPgCfgChanges.cfg_segs_low as Hsegs.
assert (Hin3 : In (3, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (frames_bounds rsegs B LAWS lyc Sc W memc mdc 3 pos HAR Hin3) as (_ & _ & Happ).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 3 pos HAR Hin3) as (_ & _ & HFpres & _).
rewrite <- HF in Happ, HFpres. change (fs_frame_bytes 3) with 512 in Happ, HFpres.
unfold T_SEG_STK, ASTACK in HspR, Hdisw.
(* the closed bounds the entry state asks for *)
assert (HpcD4 : 0 <= W6B_D4) by (unfold W6B_D4; lia).
assert (HRa : alloc_ceiling <= R) by lia.
assert (HRb : R + 0x1a0 <= 2 ^ 47) by lia.
assert (Hcb : 1 <= c <= 2 ^ 47 - 1).
{ unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham. lia. }
assert (Hnl : 0 <= Z.of_nat (length r) + 1 < 2 ^ 64) by lia.
assert (Hpp0 : 0 <= pp) by lia.
assert (Hshdw : forall a, F + 0xf0 <= a < F + 0x158 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 17592186044416)).
{ clear - Happ. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. intros a Ha. lia. }
assert (HpR : forall o, (0xc8 <= o < 0xd0 \/ 0xf8 <= o < 0x100) -> apresent (w_H W) memc (R + o)).
{ intros o Ho. apply Hpres. lia. }
assert (HpE : forall o, 0 <= o < 104 -> apresent (w_H W) memc (F + 0xf0 + o)).
{ intros o Ho. apply (proj1 (HFpres (F + 0xf0 + o) ltac:(lia))). }
destruct r as [|b0 r'].
- (* ======================= no byte is left: 0x80e68 -> 0x811c8 ======================= *)
  assert (E9 : ew (Ereg regs (eb_extra F vb (Z.of_nat (length (@nil byte)) + 1) 0)) 9 = Z_to_bv 64 R)
    by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
  assert (E23 : ew (Ereg regs (eb_extra F vb (Z.of_nat (length (@nil byte)) + 1) 0)) 23 = Z_to_bv 64 SHADOW_OFF)
    by (rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact H23).
  assert (E24 : ew (Ereg regs (eb_extra F vb (Z.of_nat (length (@nil byte)) + 1) 0)) 24 = Z_to_bv 64 c)
    by (rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact H24).
  assert (E25 : ew (Ereg regs (eb_extra F vb (Z.of_nat (length (@nil byte)) + 1) 0)) 25 = Z_to_bv 64 0)
    by (rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); rewrite H25; reflexivity).
  assert (E32 : ew (Ereg regs (eb_extra F vb (Z.of_nat (length (@nil byte)) + 1) 0)) 32 = Z_to_bv 64 F)
    by exact (ew_Ereg_extra regs _ 0).
  assert (E33 : ew (Ereg regs (eb_extra F vb (Z.of_nat (length (@nil byte)) + 1) 0)) 33 = Z_to_bv 64 vb)
    by exact (ew_Ereg_extra regs _ 1).
  assert (B9 : bv_unsigned (ew (Ereg regs (eb_extra F vb (Z.of_nat (length (@nil byte)) + 1) 0)) 9) = R)
    by (rewrite E9; apply unsigned_lit_small; lia).
  assert (B32 : bv_unsigned (ew (Ereg regs (eb_extra F vb (Z.of_nat (length (@nil byte)) + 1) 0)) 32) = F)
    by (rewrite E32; apply unsigned_lit_small; lia).
  assert (HS : st_ok rsegs (Ereg regs (eb_extra F vb (Z.of_nat (length (@nil byte)) + 1) 0)) (ss_eb W6B_D4 false)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 W6B_D4) memc (seg_rom rsegs)))).
  { apply (eb_entry W6B_D4 false W regs memc R F c vb (Z.of_nat (length (@nil byte)) + 1) 0 pp);
      try assumption; try lia; try (intros Hb; discriminate Hb). }
  assert (SHOK : sh_ok rsegs EBx eb_SH (Ereg regs (eb_extra F vb (Z.of_nat (length (@nil byte)) + 1) 0))
    (mrestrict (w_H W) memc))
    by exact (eb_shok regs (w_H W) memc F vb (Z.of_nat (length (@nil byte)) + 1) 0 H23 HFa HFb Hera Hshdw).
  assert (HAE : env_agree 32 (Ereg regs (eb_extra F vb (Z.of_nat (length (@nil byte)) + 1) 0))
    (Ereg regs (eb_extra F vb (Z.of_nat (length (@nil byte)) + 1) 0))) by apply env_agree_refl.
  unfold cfg_at. change (w64 W6B_D4) with (Z_to_bv 64 W6B_D4).
  srr_branch_tok eb_tbl_ok HS SHOK Espan.
  + (* s9 = 0: the run to J *)
    aj_run_to_tok eb_tbl_ok HS HJ SHOK Espan W6_J.
    { (* the write windows: [R+0xc8, R+0xd0) and [R+0xf8, R+0x100) in the journal's stack window, e in the
         frame (3, pos) the harness holds *)
      lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp ?fp ?bl0 ?blc ?lyx ?ow =>
        let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp fp bl0 blc lyx ow) end.
      apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
      eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
        [reflexivity | rewrite B9; lia | cbn [YP09.r_wlo YP09.r_whi]; lia
        | cbn [YP09.r_wlo YP09.r_whi]; lia |].
      eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
        [reflexivity | rewrite B9; lia | cbn [YP09.r_wlo YP09.r_whi]; lia
        | cbn [YP09.r_wlo YP09.r_whi]; lia |].
      eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32%nat F);
        [reflexivity | exact B32
        | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists 3, pos; split; [exact Hown|];
          left; unfold in_zr; cbn [fst snd]; rewrite <- HF; change (fs_frame_bytes 3) with 512; lia |].
      apply awr_ok_nil. }
    (* the leaf at J *)
    apply SRr_ret. unfold w6_post.
    lazymatch goal with
    | HS1 : st_ok _ _ _ (restrict (w_H _) ?m), HJ1 : ajournal _ _ _ _ _ _ _ _ _ _ _ ?l1 ?s1 _ _ _ _,
      HFr1 : frame_of _ _ _ _ |- _ =>
      exists l1, s1, (ms_regs m), (ms_mem m); eexists;
      split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ m HS1 eq_refl) at 1; reflexivity|];
      split; [exact HJ1|];
      split; [eapply (regs_kept_of_st_ok rsegs _ _ m _ _ (w_H W) _ HS1);
              [env_agree_chain HAE | vm_compute; reflexivity]|];
      split; [reflexivity|];
      split; [apply Permutation_refl|];
      split; [c2_kio|];
      split; [apply mo_le_refl; exact MTL|];
      split;
      [ apply (c4_keep W _ _ memc _ R F HFr1); intros rg Hin Ha Hr;
        cbn [ss_mem add_cond ss_eb eb_regions In] in Hin;
        destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val eb_rA eb_rB eb_rC eb_rE] in Hr;
        rewrite ?B9, ?B32 in Hr; unfold w6b_wr, T_SEG_STK, ASTACK; lia
      | ]
    end.
    unfold w6b_J_R. rewrite (c4_model b (@nil byte) Hkd). cbn [fuzz_u8 fst snd length Z.of_nat].
    lazymatch goal with HS1 : st_ok _ _ _ (restrict _ ?m) |- _ => rename HS1 into HSf; set (msf := m) in * end.
    split; [c2_regv HSf (20%bv : bv 5); rewrite E33, unsigned_lit_small by lia; unfold w64; f_equal; lia|].
    split; [c2_regv HSf (21%bv : bv 5); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl), H21; unfold w64;
            rewrite unsigned_lit_small by lia; f_equal; lia|].
    split; [c2_regv HSf (27%bv : bv 5); rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl), H27; unfold w64;
            rewrite unsigned_lit_small by lia; f_equal; lia|].
    split; [c2_regv HSf (25%bv : bv 5); rewrite E24, unsigned_lit_small by lia; unfold w64; f_equal; lia|].
    split.
    { eapply (tl_val_at _ _ (w_H W) msf 2%nat _ 248 8%N _ 0 R _);
        [exact HSf | reflexivity | c4_in | cbn [YP09.r_base base_val]; exact B9 | reflexivity | cbn; lia | lia]. }
    apply c4_e_image.
    * eapply (tl_val_at _ _ (w_H W) msf 3%nat _ 240 4%N _ 2 F _);
        [exact HSf | reflexivity | c4_in | cbn [YP09.r_base base_val]; exact B32 | reflexivity | cbn; lia | lia].
    * eapply (tl_val_at _ _ (w_H W) msf 3%nat _ 244 4%N _ 4 F _);
        [exact HSf | reflexivity | c4_in | cbn [YP09.r_base base_val]; exact B32 | reflexivity | cbn; lia | lia].
    * eapply (tl_val_at _ _ (w_H W) msf 3%nat _ 248 4%N _ (0 mod 3) F _);
        [exact HSf | reflexivity | c4_in | cbn [YP09.r_base base_val]; exact B32 | reflexivity | cbn; lia | lia].
    * intros i Hi. eapply (c4_zero_at _ _ (w_H W) msf 3%nat _ 252 92 _ i);
        [exact HSf | reflexivity | c4_in | cbn [YP09.r_base base_val]; rewrite B32; lia | lia].
  + (* s9 <> 0 is impossible here *)
    exfalso.
    assert (Ht : (bv_unsigned
                    (sv_denot (Ereg regs (eb_extra F vb (Z.of_nat (length (@nil byte)) + 1) 0)) (SOff 25 0)) =?
                  bv_unsigned
                    (sv_denot (Ereg regs (eb_extra F vb (Z.of_nat (length (@nil byte)) + 1) 0)) (SLit 0))) = false)
      by exact Hc.
    cbn [sv_denot] in Ht. rewrite E25 in Ht. discriminate Ht.
- (* ======================= a byte is left ======================= *)
  assert (Hb0 : 0 <= bv_unsigned b0 < 256) by apply Cursor.byte_range.
  assert (E9 : ew (Ereg regs (eb_extra F vb (Z.of_nat (length (b0 :: r')) + 1) (bv_unsigned b0))) 9 = Z_to_bv 64 R)
    by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
  assert (E14 : ew (Ereg regs (eb_extra F vb (Z.of_nat (length (b0 :: r')) + 1) (bv_unsigned b0))) 14
    = Z_to_bv 64 (c - 1)) by (rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact H14).
  assert (E23 : ew (Ereg regs (eb_extra F vb (Z.of_nat (length (b0 :: r')) + 1) (bv_unsigned b0))) 23
    = Z_to_bv 64 SHADOW_OFF) by (rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact H23).
  assert (E24 : ew (Ereg regs (eb_extra F vb (Z.of_nat (length (b0 :: r')) + 1) (bv_unsigned b0))) 24 = Z_to_bv 64 c)
    by (rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact H24).
  assert (E25 : ew (Ereg regs (eb_extra F vb (Z.of_nat (length (b0 :: r')) + 1) (bv_unsigned b0))) 25
    = Z_to_bv 64 (Z.of_nat (length (b0 :: r')))) by (rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
  assert (E32 : ew (Ereg regs (eb_extra F vb (Z.of_nat (length (b0 :: r')) + 1) (bv_unsigned b0))) 32 = Z_to_bv 64 F)
    by exact (ew_Ereg_extra regs _ 0).
  assert (E33 : ew (Ereg regs (eb_extra F vb (Z.of_nat (length (b0 :: r')) + 1) (bv_unsigned b0))) 33
    = Z_to_bv 64 vb) by exact (ew_Ereg_extra regs _ 1).
  assert (E34 : ew (Ereg regs (eb_extra F vb (Z.of_nat (length (b0 :: r')) + 1) (bv_unsigned b0))) 34
    = Z_to_bv 64 (Z.of_nat (length (b0 :: r')) + 1)) by exact (ew_Ereg_extra regs _ 2).
  assert (E35 : ew (Ereg regs (eb_extra F vb (Z.of_nat (length (b0 :: r')) + 1) (bv_unsigned b0))) 35
    = Z_to_bv 64 (bv_unsigned b0)) by exact (ew_Ereg_extra regs _ 3).
  assert (B9 : bv_unsigned (ew (Ereg regs (eb_extra F vb (Z.of_nat (length (b0 :: r')) + 1) (bv_unsigned b0))) 9) = R)
    by (rewrite E9; apply unsigned_lit_small; lia).
  assert (B32 : bv_unsigned (ew (Ereg regs (eb_extra F vb (Z.of_nat (length (b0 :: r')) + 1) (bv_unsigned b0))) 32) = F)
    by (rewrite E32; apply unsigned_lit_small; lia).
  assert (Hm0 : val_mem rsegs (mrestrict (w_H W) memc) (c + 0) 1 (bv_unsigned b0))
    by (destruct (Hg 0%nat ltac:(cbn [length map]; lia)) as [Hv _]; exact Hv).
  rewrite Z.add_0_r in Hm0.
  assert (HS : st_ok rsegs (Ereg regs (eb_extra F vb (Z.of_nat (length (b0 :: r')) + 1) (bv_unsigned b0)))
    (ss_eb W6B_D4 true) (restrict (w_H W) (mkst regs (Z_to_bv 64 W6B_D4) memc (seg_rom rsegs)))).
  { apply (eb_entry W6B_D4 true W regs memc R F c vb (Z.of_nat (length (b0 :: r')) + 1) (bv_unsigned b0) pp);
      try assumption; try lia.
    intros _. split; [exact Hm0|].
    pose proof (Hdisw c ltac:(cbn [length]; lia)) as Hd1.
    pose proof (Hdis c ltac:(cbn [length]; lia)) as Hd2.
    split; lia. }
  assert (SHOK : sh_ok rsegs EBx eb_SH
    (Ereg regs (eb_extra F vb (Z.of_nat (length (b0 :: r')) + 1) (bv_unsigned b0))) (mrestrict (w_H W) memc))
    by exact (eb_shok regs (w_H W) memc F vb (Z.of_nat (length (b0 :: r')) + 1) (bv_unsigned b0)
         H23 HFa HFb Hera Hshdw).
  assert (HAE : env_agree 32 (Ereg regs (eb_extra F vb (Z.of_nat (length (b0 :: r')) + 1) (bv_unsigned b0)))
    (Ereg regs (eb_extra F vb (Z.of_nat (length (b0 :: r')) + 1) (bv_unsigned b0)))) by apply env_agree_refl.
  unfold cfg_at. change (w64 W6B_D4) with (Z_to_bv 64 W6B_D4).
  srr_branch_tok eb_tbl_ok HS SHOK Espan.
  + (* s9 = 0 is impossible here *)
    exfalso.
    assert (Ht : (bv_unsigned
                    (sv_denot (Ereg regs (eb_extra F vb (Z.of_nat (length (b0 :: r')) + 1) (bv_unsigned b0)))
                       (SOff 25 0)) =?
                  bv_unsigned
                    (sv_denot (Ereg regs (eb_extra F vb (Z.of_nat (length (b0 :: r')) + 1) (bv_unsigned b0)))
                       (SLit 0))) = true) by exact Hc.
    cbn [sv_denot] in Ht. rewrite E25 in Ht.
    rewrite (unsigned_lit_small (Z.of_nat (length (b0 :: r'))) ltac:(lia)) in Ht.
    rewrite (unsigned_lit_small (Z.of_nat (length (b0 :: r')) + 0) ltac:(lia)) in Ht.
    rewrite (unsigned_lit_small 0 ltac:(lia)) in Ht.
    apply Z.eqb_eq in Ht. cbn [length] in Ht. lia.
  + (* s9 <> 0: the read of the input byte and the run to J *)
    aj_run_to_tok eb_tbl_ok HS HJ SHOK Espan W6_J.
    { (* the instrumented check of the cursor: its one byte is addressable *)
      apply (obl_of_range rsegs (w_H W) memc _ EBx _ _ c (Z.of_nat (length (b0 :: r'))) Hrain).
      - apply (U_atom _ 23 SHADOW_OFF E23). unfold SHADOW_OFF. lia.
      - rewrite (U_atom _ 24 c E24) by lia. lia.
      - rewrite (U_atom _ 24 c E24) by lia. cbn [length]. lia. }
    { lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp ?fp ?bl0 ?blc ?lyx ?ow =>
        let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp fp bl0 blc lyx ow) end.
      apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
      eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
        [reflexivity | rewrite B9; lia | cbn [YP09.r_wlo YP09.r_whi]; lia
        | cbn [YP09.r_wlo YP09.r_whi]; lia |].
      eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
        [reflexivity | rewrite B9; lia | cbn [YP09.r_wlo YP09.r_whi]; lia
        | cbn [YP09.r_wlo YP09.r_whi]; lia |].
      eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32%nat F);
        [reflexivity | exact B32
        | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists 3, pos; split; [exact Hown|];
          left; unfold in_zr; cbn [fst snd]; rewrite <- HF; change (fs_frame_bytes 3) with 512; lia |].
      apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
      apply awr_ok_nil. }
    (* the leaf at J *)
    apply SRr_ret. unfold w6_post.
    lazymatch goal with
    | HS1 : st_ok _ _ _ (restrict (w_H _) ?m), HJ1 : ajournal _ _ _ _ _ _ _ _ _ _ _ ?l1 ?s1 _ _ _ _,
      HFr1 : frame_of _ _ _ _ |- _ =>
      exists l1, s1, (ms_regs m), (ms_mem m); eexists;
      split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ m HS1 eq_refl) at 1; reflexivity|];
      split; [exact HJ1|];
      split; [eapply (regs_kept_of_st_ok rsegs _ _ m _ _ (w_H W) _ HS1);
              [env_agree_chain HAE | vm_compute; reflexivity]|];
      split; [reflexivity|];
      split; [apply Permutation_refl|];
      split; [c2_kio|];
      split; [apply mo_le_refl; exact MTL|];
      split;
      [ apply (c4_keep W _ _ memc _ R F HFr1); intros rg Hin Ha Hr;
        cbn [ss_mem add_cond ss_eb eb_regions In] in Hin;
        destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]];
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val eb_rA eb_rB eb_rC eb_rE eb_rI] in Hr;
        rewrite ?B9, ?B32 in Hr; unfold w6b_wr, T_SEG_STK, ASTACK; lia
      | ]
    end.
    unfold w6b_J_R. rewrite (c4_model b (b0 :: r') Hkd). cbn [fuzz_u8 fst snd].
    lazymatch goal with HS1 : st_ok _ _ _ (restrict _ ?m) |- _ => rename HS1 into HSf; set (msf := m) in * end.
    split; [c2_regv HSf (20%bv : bv 5); rewrite E33, unsigned_lit_small by lia; unfold w64; f_equal; lia|].
    split; [c2_regv HSf (21%bv : bv 5); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl), H21; unfold w64;
            rewrite unsigned_lit_small by lia; f_equal; lia|].
    split; [c2_regv HSf (27%bv : bv 5); rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl), H27; unfold w64;
            rewrite unsigned_lit_small by lia; f_equal; lia|].
    split; [c2_regv HSf (25%bv : bv 5); rewrite E14, unsigned_lit_small by lia; unfold w64; f_equal;
            cbn [length]; lia|].
    split.
    { eapply (tl_val_at _ _ (w_H W) msf 2%nat _ 248 8%N _ (Z.of_nat (length r')) R _);
        [exact HSf | reflexivity | c4_in | cbn [YP09.r_base base_val]; rewrite ?ew_ewset_other by lia; exact B9
        | cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite E34, unsigned_lit_small by lia; f_equal;
          cbn [length]; lia
        | cbn; lia | lia]. }
    apply c4_e_image.
    * eapply (tl_val_at _ _ (w_H W) msf 3%nat _ 240 4%N _ 2 F _);
        [exact HSf | reflexivity | c4_in
        | cbn [YP09.r_base base_val]; rewrite ?ew_ewset_other by lia; exact B32 | reflexivity | cbn; lia | lia].
    * eapply (tl_val_at _ _ (w_H W) msf 3%nat _ 244 4%N _ 4 F _);
        [exact HSf | reflexivity | c4_in
        | cbn [YP09.r_base base_val]; rewrite ?ew_ewset_other by lia; exact B32 | reflexivity | cbn; lia | lia].
    * eapply (tl_val_at _ _ (w_H W) msf 3%nat _ 248 4%N c4_a0 (bv_unsigned b0 mod 3) F _);
        [exact HSf | reflexivity | c4_in
        | cbn [YP09.r_base base_val]; rewrite ?ew_ewset_other by lia; exact B32
        | apply c4_a0_val; [rewrite ?ew_ewset_other by lia; exact E35 | exact Hb0]
        | cbn; lia | lia].
    * intros i Hi. eapply (c4_zero_at _ _ (w_H W) msf 3%nat _ 252 92 _ i);
        [exact HSf | reflexivity | c4_in
        | cbn [YP09.r_base base_val]; rewrite ?ew_ewset_other by lia; rewrite B32; lia | lia].
Qed.

End d.
End b.

Print Assumptions w6b_c4.
