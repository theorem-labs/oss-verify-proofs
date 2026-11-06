(* check_no_overread 0x811c8 (fs.asan), a Theorem Labs lane: the three preset_base64_decode call steps (0x81398 / 0x813a8 /
   0x813b8, callee 0x8481c, ra 0x8139c / 0x813ac / 0x813bc), proving FSW_check_no_overread.v's cno_call_dec_T (the
   call-step interface: cno_site at the callee's entry, cno_ret at the return address) from S0's decode_spec_ff
   (lib/A/FSH_Fn_writer.v), and the three R2 branch lemmas the top file's run uses at 0x813c8 / 0x813d4 / 0x813e4.
   All three calls decode the same C string c_db, so b64_dec (c_db cx) decides the arm of every call: None (each call
   allocates and frees inside, a0 = 0, *lenp keeps its value) or Some out (each buffer stays live, a0 = q <> 0,
   *lenp = length out). The refused arm of decode_spec_ff is dead: quiet gives g_fail_at = SIZE_MAX.
   Template (text only): a Theorem Labs lane's crcs walk, a working branch 7f69688b4f6
   lib/A/FSH_check_reject_clean_starved.v (crcs_call / crcs_site / the decode site at 0x82630, crcs_roP_notFP,
   crcs_text_nf); the bespoke A proofs on a working branch were read for the stage facts only. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
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
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_ret
FSW_rres FSW_frame FSH_Fn_cno FSH_Fn_alloc FSW_check_no_overread_tbl
FSW_check_no_overread.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSH_Fn_writer FSW_strkit FSW_rd.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================= pure facts ================= *)
(* the decoder's footprint (fuzz/alloc.c's statics and *lenp) holds no byte 0, so the sink stays closed *)
Lemma cno_dfp_closed : forall lenp, 0 < lenp -> ~ YI16.sink_open_fp (FS_PSTAT_FP ++ [(lenp, lenp + 8)]).
Proof.
intros lenp Hl (r & Hr & H). apply in_app_or in Hr.
destruct Hr as [Hr | [<- | []]]; [unfold FS_PSTAT_FP in Hr; destruct Hr as [<-|[<-|[<-|[<-|[]]]]] |];
  cbn [fst snd] in H; lia.
Qed.
(* a byte of the decoder's footprint is a static (an image byte) or a byte of *lenp *)
Lemma cno_dfp_img : forall lenp a, inFP (FS_PSTAT_FP ++ [(lenp, lenp + 8)]) a -> in_img tfibsegs a \/ lenp <= a < lenp + 8.
Proof.
intros lenp a (r & Hr & H1 & H2). apply in_app_or in Hr. destruct Hr as [Hr | [<- | []]].
- left. apply cno_pstat_img. exists r. split; [exact Hr | lia].
- right. cbn [fst snd] in H1, H2. lia.
Qed.
(* no read-only byte is a static (port of crcs_roP_notFP, a working branch) *)
Lemma cno_roP_notFP : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP FS_PSTAT_FP a.
Proof.
intros a Ha (r & Hr & H1 & H2).
assert (Hx : forallb (fun s => seg_writable s || forallb (fun r => (snd r <=? Z.of_N (seg_base s)) ||
  (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? fst r)) FS_PSTAT_FP) tfibsegs = true) by (vm_compute; reflexivity).
destruct Ha as [(sg & Hin & Hw & Hs) | Hr2].
- pose proof (proj1 (forallb_forall _ _) Hx sg Hin) as Hs'. cbv beta in Hs'. rewrite Hw in Hs'. cbn [orb] in Hs'.
  pose proof (proj1 (forallb_forall _ _) Hs' r Hr) as Hr'.
  apply Bool.orb_true_iff in Hr' as [Hr'|Hr']; apply Z.leb_le in Hr'; lia.
- unfold FS_PSTAT_FP in Hr. unfold FS_RLO, FS_RHI in Hr2.
  destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in H1, H2; lia.
Qed.
Lemma cno_dsize_pos : forall tb, 3 <= FSH_Fn_writer.dec_size tb.
Proof.
intros tb. unfold FSH_Fn_writer.dec_size.
pose proof (Z.div_pos (Z.of_nat (length tb)) 4 ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma cno_pw_last : forall {X} (R : X -> X -> Prop) (l : list X) x y, YG0f.pairwise R (l ++ [x]) -> In y l -> R y x.
Proof.
intros X R l. induction l as [|z l IH]; intros x y H Hy; [destruct Hy|].
cbn [app YG0f.pairwise] in H. destruct H as (HF & HP). destruct Hy as [<- | Hy].
- apply (proj1 (Forall_forall _ _) HF). apply in_or_app. right. left. reflexivity.
- exact (IH x y HP Hy).
Qed.

(* ================= the R2 arms after the third decode (0x813c8 / 0x813d4 / 0x813e4 -> 0x81548) =================
   The top's run stops at each branch (MEASURED from cno_ss 0x813bc 19 18 [] []: SR_branch BC_EQ at 0x813c8 with the
   two expressions below, SR_branch BC_EQ at 0x813d4 with the xor against 0); these lemmas add the NOT-TAKEN
   condition, from the decode answers: s6 = q1 (atom 22), s8 = q2 (atom 24), a0 = q3 (atom 10), null together. *)
Section BR. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma cno_br_813c8 : forall E ss ms q1 q3,
  st_ok tfibsegs E ss ms -> ew E 22 = w64 q1 -> ew E 10 = w64 q3 -> 0 <= q1 < 2 ^ 64 -> 0 <= q3 < 2 ^ 64 ->
  (q1 = 0 <-> q3 = 0) ->
  st_ok tfibsegs E (add_cond ss (mkAC BC_NE (SAlu ALU_SLTU (SLit 0) (SOff 22 0)) (SAlu ALU_SLTU (SOff 10 0) (SLit 1))))
    ms.
Proof.
intros E ss ms q1 q3 HS E22 E10 H1 H3 Hiff.
apply (st_ok_add_cond_neg tfibsegs E ss ms BC_EQ _ _ HS).
rewrite branch_eq_U, !U_SAlu. cbn [zalu_raw].
rewrite (U_lit E 0) by lia. rewrite (U_lit E 1) by lia.
rewrite (U_atom E 22 q1 E22 H1), (U_atom E 10 q3 E10 H3).
destruct (Z.eq_dec q1 0) as [Hz | Hz].
- assert (Hq3 : q3 = 0) by (apply Hiff; exact Hz). subst q1 q3. reflexivity.
- assert (Hq3 : q3 <> 0) by (intros Ez; apply Hz; apply Hiff; exact Ez).
  rewrite (proj2 (Z.ltb_lt 0 q1)) by lia. rewrite (proj2 (Z.ltb_ge q3 1)) by lia. reflexivity.
Qed.
Lemma cno_br_813d4 : forall E ss ms q2 q3,
  st_ok tfibsegs E ss ms -> ew E 24 = w64 q2 -> ew E 10 = w64 q3 -> 0 <= q2 < 2 ^ 64 -> 0 <= q3 < 2 ^ 64 ->
  (q2 = 0 <-> q3 = 0) ->
  st_ok tfibsegs E (add_cond ss (mkAC BC_NE
    (SAlu ALU_XOR (SAlu ALU_SLTU (SLit 0) (SOff 24 0)) (SAlu ALU_SLTU (SOff 10 0) (SLit 1))) (SLit 0))) ms.
Proof.
intros E ss ms q2 q3 HS E24 E10 H2 H3 Hiff.
apply (st_ok_add_cond_neg tfibsegs E ss ms BC_EQ _ _ HS).
rewrite branch_eq_U, !U_SAlu. cbn [zalu_raw].
rewrite (U_lit E 0) by lia. rewrite (U_lit E 1) by lia.
rewrite (U_atom E 24 q2 E24 H2), (U_atom E 10 q3 E10 H3).
destruct (Z.eq_dec q2 0) as [Hz | Hz].
- assert (Hq3 : q3 = 0) by (apply Hiff; exact Hz). subst q2 q3. reflexivity.
- assert (Hq3 : q3 <> 0) by (intros Ez; apply Hz; apply Hiff; exact Ez).
  rewrite (proj2 (Z.ltb_lt 0 q2)) by lia. rewrite (proj2 (Z.ltb_ge q3 1)) by lia. reflexivity.
Qed.
(* 0x813e4 `bne s10, a0`: the two loaded lengths *lenp of the first and third decode, the same length out *)
Lemma cno_br_813e4 : forall E ss ms x y n,
  st_ok tfibsegs E ss ms -> sv_denot E x = w64 n -> sv_denot E y = w64 n ->
  st_ok tfibsegs E (add_cond ss (mkAC BC_EQ x y)) ms.
Proof.
intros E ss ms x y n HS Hx Hy.
apply (st_ok_add_cond_neg tfibsegs E ss ms BC_NE x y HS).
rewrite branch_ne_U. unfold U. rewrite Hx, Hy, Z.eqb_refl. reflexivity.
Qed.

End BR.

(* ================= the call step ================= *)
Section P. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the callee contract, CTX-free (a working branch: the CTX drop removed its call-trace premise and binder,
   so this call step takes no call-trace row) *)
Hypothesis DEC : FSH_Fn_writer.decode_spec_ff B tfibsegs.
Hypothesis IMG : fs_img_facts tfibsegs B.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* the decoder's post (fpostU at its own sp, footprint statics + *lenp) as the walk's cno_ret: FSW_check_no_overread.v
   cno_after_pcall's proof (journals composed, zone and blocks kept by the callee journal), with the callee journal
   handed to the P obligation (cno_strs_kept needs it) *)
Lemma cno_dec_ret : forall cx k ly S U (W : world tfibsegs) regs mem md lenp kc U'
    (Q P : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) W' c',
  cno_base B cx -> cno_site B cx k ly S U W regs mem md ->
  cno_F cx + 32 <= lenp -> lenp + 8 <= cno_F cx + 128 ->
  (forall ly2 S2 W2 regs2 mem2 md2,
     ajournal tfibsegs B STK_preset_base64_decode (spZ regs) (FS_PSTAT_FP ++ [(lenp, lenp + 8)]) ly S W
       (unpoison U mem) md [] ly2 S2 W2 (unpoison U' mem2) md2 kc ->
     upoison_ok B ly2 S2 U' -> upoisoned tfibsegs W2 mem2 U' ->
     Q ly2 S2 W2 regs2 mem2 md2 -> FSupoisonU.fs_heads B ly2 S2 U' /\ P ly2 S2 W2 regs2 mem2 md2) ->
  fpostU tfibsegs B STK_preset_base64_decode (spZ regs) (FS_PSTAT_FP ++ [(lenp, lenp + 8)]) regs ly S U W mem md
    kc U' Q W' c' ->
  cno_ret B cx k ly S regs mem W kc U' (fun a => lenp <= a < lenp + 8) P W' c'.
Proof.
intros cx k ly S U W regs mem md lenp kc U' Q P W' c' HB HS Hl1 Hl2 HQP HPOST.
destruct HPOST as (ly' & S' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HP & HQ).
destruct (HQP ly' S' W' regs' mem' md' HJc OK' PO' HQ) as (Hh' & HP').
pose proof HS as (HJ & HARU & _ & R2 & R8 & _).
pose proof (cno_nums B cx HB) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof cno_stk as FS.
assert (SDEC : STK_preset_base64_decode = 16528) by reflexivity.
assert (Esp : spZ regs = cno_sp1 cx) by (unfold spZ; rewrite R2; unfold w64; apply wz; lia).
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _).
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
assert (Hin : In (1, c_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EF : ly_F ly = ly_F (c_ly cx)) by (destruct Hly as (_ & _ & _ & _ & _ & E & _); exact E).
assert (EFa : frame_addr ly 1 (c_fpos cx) = cno_F cx) by (unfold cno_F, frame_addr; rewrite EF; reflexivity).
destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison U mem) md 1 (c_fpos cx) HAR Hin) as (H4096 & HFc & Happ).
change (fs_frame_bytes 1) with 128 in H4096, HFc, Happ. rewrite EFa in H4096, HFc, Happ.
pose proof (shadow_addr_bounds (cno_F cx) ltac:(lia)) as (Hs1 & Hs2).
pose proof (cno_frame_shadow_disj (cno_F cx) ltac:(lia) Happ) as HFS.
assert (HFPsub : forall a, inFP (FS_PSTAT_FP ++ [(lenp, lenp + 8)]) a ->
   (inFP FS_PSTAT_FP a /\ exists b n, In (b, n) (ablocks B ly S) /\ b <= a < b + req_size n) \/
   in_tmp_block (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly S) a \/
   (inFP FS_PSTAT_FP a /\ in_img tfibsegs a) \/ in_frames ly [(1, c_fpos cx)] a).
{ intros a (r & Hr & H1 & H2). apply in_app_or in Hr. destruct Hr as [Hr | [<- | []]].
  - right; right; left. assert (Hf : inFP FS_PSTAT_FP a) by (exists r; split; [exact Hr | lia]).
    split; [exact Hf | exact (cno_pstat_img a Hf)].
  - right; right; right. cbn [fst snd] in H1, H2. exists 1, (c_fpos cx). split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite EFa. change (fs_frame_bytes 1) with 128. lia. }
assert (HJ2 : cno_J B cx (k + kc) ly' S' W' (unpoison U' mem') md').
{ exact (fsw_ajournal_sub4 B STK_check_no_overread (cno_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(1, c_fpos cx)] ly S W (unpoison U mem) md k STK_preset_base64_decode
    (spZ regs) (FS_PSTAT_FP ++ [(lenp, lenp + 8)]) [] ly' S' W' (unpoison U' mem') md' kc HJ HJc
    ltac:(rewrite Esp, SDEC, FS; lia) ltac:(rewrite Esp; lia) HFPsub). }
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md') by (split; [exact (proj1 HJ2) | split; [exact OK' | exact PO']]).
pose proof HJ2 as (_ & Hly2 & _ & _ & _ & Hfrs2 & _).
assert (Hin2 : In (1, c_fpos cx) (frames S')) by (rewrite Hfrs2; left; reflexivity).
assert (EF2 : ly_F ly' = ly_F (c_ly cx)) by (destruct Hly2 as (_ & _ & _ & _ & _ & E & _); exact E).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & _ & G4 & _).
exists ly', S', regs', mem', md'.
split; [rewrite Ec; unfold cfg_at, w64, raZ; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [exact HJ2|]. split; [exact HARU'|]. split; [exact Hh'|]. split; [exact HP|].
split; [|split; [|exact HP']].
- intros a Hz HnK. cbv beta in HnK.
  rewrite <- (cno_zone_unp B cx ly' S' U' W' mem' md' a HB HARU' Hin2 EF2 Hz).
  rewrite <- (cno_zone_unp B cx ly S U W mem md a HB HARU Hin EF Hz).
  unfold cno_zone, cno_SF in Hz.
  assert (HnF : ~ inFP (FS_PSTAT_FP ++ [(lenp, lenp + 8)]) a).
  { intros Hf. destruct (cno_dfp_img lenp a Hf) as [Hi | Hl]; [|exact (HnK Hl)].
    pose proof (fs_segs_img a Hi) as Hb. unfold FS_IMG_END in Hb.
    destruct Hz as [Hz | [Hz | [Hz | Hz]]]; [lia | lia | | lia].
    apply (frm_img tfibsegs B LAWS ly S W (unpoison U mem) md 1 (c_fpos cx) a HAR Hin); [|exact Hi].
    rewrite EFa. change (fs_frame_bytes 1) with 128. lia. }
  destruct Hz as [Hz | [Hz | [Hz | Hz]]].
  + apply G1; [lia | rewrite Esp; lia].
  + apply G1; [lia | rewrite Esp; lia].
  + apply (G4 1 (c_fpos cx) a Hin); [left | exact HnF].
    unfold frame_rng, in_zr. cbn [fst snd]. rewrite EFa. change (fs_frame_bytes 1) with 128. lia.
  + apply (G4 1 (c_fpos cx) a Hin); [right | exact HnF].
    unfold in_zr. cbn [fst snd]. rewrite EFa. change (fs_frame_bytes 1 / 8) with 16. lia.
- intros p n i Hp Hp' Hi HnK. cbv beta in HnK.
  rewrite <- (cno_blk_unp B ly' S' U' W' mem' md' p n i HARU' Hp' Hi).
  rewrite <- (cno_blk_unp B ly S U W mem md p n i HARU Hp Hi).
  apply (G2 p n i Hp Hp' Hi). intros Hx.
  destruct (cno_dfp_img lenp (p + i) Hx) as [Hi' | Hl]; [|exact (HnK Hl)].
  exact (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md p n (p + i) HAR Hp ltac:(lia) Hi').
Qed.

(* the kept-string clause: a block string (tail word in the block) off U survives the decoder (FSW_rd
   cstr_ok_kept_call: its bytes are off the footprint), and every new range of U' misses every old block *)
Lemma cno_strs_kept : forall ly S U (W : world tfibsegs) mem md pos lenp STK1 sp1 ly' S' U' W' mem' md' kc,
  ARU tfibsegs B ly S U W mem md -> In (1, pos) (frames S) ->
  frame_addr ly 1 pos <= lenp -> lenp + 8 <= frame_addr ly 1 pos + 128 -> 0 < lenp ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem) ->
  ajournal tfibsegs B STK1 sp1 (FS_PSTAT_FP ++ [(lenp, lenp + 8)]) ly S W (unpoison U mem) md [] ly' S' W'
    (unpoison U' mem') md' kc ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  (forall r, In r U' -> In r U \/
     forall b m, In (b, m) (ablocks B ly S) -> fst r + snd r <= b \/ b + req_size m <= fst r) ->
  cno_dec_strs B ly S U W mem W' mem' U'.
Proof.
intros ly S U W mem md pos lenp STK1 sp1 ly' S' U' W' mem' md' kc HARU Hin Hl1 Hl2 Hl0 HRO HJc OK' PO' Hav
  p l b m Hb Hbp Hpl HUav Hc.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
pose proof (sep_block_frame tfibsegs B LAWS ly S W (unpoison U mem) md b m 1 pos HAR Hb Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd.
assert (Hrq : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
assert (HU2 : forall r, In r U' -> In r U \/ fst r + snd r <= p \/ p + Z.of_nat (length l) + 1 <= fst r).
{ intros r Hr. destruct (Hav r Hr) as [HrU | Hav']; [left; exact HrU|]. right.
  destruct (Hav' b m Hb) as [H | H]; [left; lia | right; lia]. }
assert (HF : forall a, p <= a < p + Z.of_nat (length l) + 8 -> ~ inFP (FS_PSTAT_FP ++ [(lenp, lenp + 8)]) a).
{ intros a Ha Hf. destruct (cno_dfp_img lenp a Hf) as [Hi | Hl].
  - exact (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md b m a HAR Hb ltac:(lia) Hi).
  - lia. }
assert (Hro : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP (FS_PSTAT_FP ++ [(lenp, lenp + 8)]) a).
{ intros a Ha (r & Hr & H1 & H2). apply in_app_or in Hr. destruct Hr as [Hr | [<- | []]].
  - exact (cno_roP_notFP a Ha (ex_intro _ r (conj Hr (conj H1 H2)))).
  - cbn [fst snd] in H1, H2.
    apply (frm_img tfibsegs B LAWS ly S W (unpoison U mem) md 1 pos a HAR Hin); [|exact (FSW_rd.fsw_roP_img a Ha)].
    change (fs_frame_bytes 1) with 128. lia. }
pose proof (FSW_rd.arodata_kept B STK1 sp1 _ ly S U W mem md ly' S' U' W' mem' md' kc HJc HARU OK' PO'
  (cno_dfp_closed lenp Hl0) Hro HRO) as HRO'.
assert (Hk : cstr_kept B ly S U p l).
{ left. exists b, m. split; [exact Hb|]. split; [exact Hbp|]. split; [lia | exact HUav]. }
destruct (FSW_rd.cstr_ok_kept_call B STK1 sp1 _ ly S U W mem md ly' S' U' W' mem' md' kc p l HJc HARU OK' PO' HF HU2
  IMG HRO' Hk Hc) as (Hc' & _).
split; [exact Hc'|].
intros r Hr. destruct (HU2 r Hr) as [HrU | [H | H]]; [exact (HUav r HrU) | right; exact H | left; exact H].
Qed.

Lemma cno_call_dec : cno_call_dec_T B.
Proof.
intros cx k ly S U W regs mem md text lenp v live peak cnt fail HB HS Hra R10 R11 Hcs Hsrc Hsh Hv Hv64 Hg Hq Hlv Hk
  Hbb.
pose proof (cno_nums B cx HB) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof cno_stk as FS.
assert (SDEC : STK_preset_base64_decode = 16528) by reflexivity.
pose proof (cno_fpre B cx k ly S U W regs mem md STK_preset_base64_decode HB HS ltac:(rewrite SDEC; lia)
  ltac:(rewrite SDEC, FS; lia)) as HPREc.
pose proof (cno_arodata B cx k ly S U W mem md HB (proj1 HS) (proj1 (proj2 HS))) as HRO.
pose proof HB as (HPRE & _ & Hfr0 & _ & _ & _ & Hsrc0 & _ & _ & Hn & _ & _ & _ & Hev & _).
pose proof HS as (HJ & HARU & Hheads & _).
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & Hnev & _).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (pos := c_fpos cx) in *.
assert (EFa : frame_addr ly 1 pos = cno_F cx) by (unfold cno_F, frame_addr; rewrite EF; reflexivity).
assert (Hin : In (1, pos) (frames S)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS ly S W (unpoison U mem) md 1 pos HAR Hin) as (Hal32 & _ & Hfp & _).
destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison U mem) md 1 pos HAR Hin) as (H4096 & HFc & _).
change (fs_frame_bytes 1) with 128 in Hfp, H4096, HFc.
rewrite EFa in Hal32, Hfp, H4096, HFc.
assert (Hlm : lenp mod 8 = 0 /\ cno_F cx + 32 <= lenp /\ lenp + 8 <= cno_F cx + 104).
{ destruct Hra as [(_ & E) | [(_ & E) | (_ & E)]]; rewrite E; (split; [|lia]);
    Z.div_mod_to_equations; lia. }
destruct Hlm as (Hlm & Hl1 & Hl2).
destruct Hsrc as (b & m & Hb & Hbt & Htm & HUav).
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md b m HAR Hb) as (_ & Hb4 & _).
pose proof (sep_block_frame tfibsegs B LAWS ly S W (unpoison U mem) md b m 1 pos HAR Hb Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd. rewrite EFa in Hd.
assert (Hrq : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
unfold cno_n in Htm, HUav, Hn.
(* decode_spec_ff's premises, one by one *)
assert (HFRL : Z.of_nat (length (frames S)) <= FRL_CRT_CALLEE)
  by (rewrite Hfrs; exact (cno_frames_callee (1, pos) (frames (c_S cx)) Hfr0)).
assert (HW : FSH_Fn_writer.wsrc_kept B tfibsegs ly S U W mem 0 text (c_db cx ++ [0])).
{ unfold FSH_Fn_writer.wsrc_kept. right; right; left. exists b, m.
  rewrite length_app. cbn [length]. unfold HEAD.
  split; [lia|]. split; [exact Hb|]. split; [exact Hbt|]. split; [lia|].
  intros r Hr. destruct (HUav r Hr) as [H | H]; [right | left]; lia. }
assert (Hbo : WriterSpec.bytes_ok (c_db cx)) by exact (garr8_bytes_ok tfibsegs _ _ _ (proj1 Hsrc0)).
assert (Hlen : Z.of_nat (length (c_db cx)) <= 2 ^ 28) by (unfold PRESET_FILE_MAX_BYTES in Hn; lia).
assert (Hex : exists cid pos', In (cid, pos') (frames S) /\
  forall a, lenp <= a < lenp + 8 -> in_zr a (frame_rng ly (cid, pos'))).
{ exists 1, pos. split; [exact Hin|]. intros a Ha. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFa.
  change (fs_frame_bytes 1) with 128. lia. }
assert (Hap : forall a, lenp <= a < lenp + 8 -> apresent (w_H W) mem a).
{ intros a Ha. destruct (Hfp a ltac:(lia)) as (Hp & Hno).
  exact (fsw_apresent_notowned B ly S U W mem md a HARU ltac:(lia) Hno Hp). }
assert (Hdisj : lenp + 8 <= text \/ text + Z.of_nat (length (c_db cx)) + 1 <= lenp)
  by (destruct Hd as [Hd | Hd]; [right | left]; lia).
assert (Hnev' : st_nev S + FSH_Fn_writer.dec_ev (c_db cx) <= EV_MAX) by lia.
assert (Hc1 : cnt + 1 < 2 ^ 64) by (destruct Hq as (_ & _ & Hq1); lia).
pose proof (DEC ly S U W regs mem md _ text lenp (c_db cx) live peak cnt fail v HPREc Hheads HFRL R10 R11 Hcs HW
  Hbo Hlen Hlm Hex Hap Hsh Hv Hv64 Hdisj Hg Hnev' Hbb Hlv Hc1) as HDEC.
apply (SRr_mono tfibsegs _ _ _ _ HDEC).
intros W' c' _ [[Heq _] | [(Hne & Hb64 & HPOST) | (q & out & Hne & Hb64 & Hq0 & HPOST)]].
- exfalso. destruct Hq as (Hf & _ & Hq1). unfold SIZE_MAXZ in Hf. lia.
- left. split; [exact Hb64|].
  refine (cno_dec_ret cx k ly S U W regs mem md lenp _ _ _ _ W' c' HB HS Hl1 ltac:(lia) _ HPOST).
  intros ly2 S2 W2 regs2 mem2 md2 HJc OK2 PO2 HQ. cbv beta in HQ. destruct HQ as (Q10 & Qab & Qv & Qg).
  split.
  + intros r Hr. destruct (Hheads r Hr) as (E16 & m' & Hm' & Hrq'). split; [exact E16|]. exists m'.
    split; [rewrite Qab; exact Hm' | exact Hrq'].
  + split; [exact Q10|]. split; [exact Qab|]. split; [exact Qv|]. split.
    * rewrite (cno_tick cnt ltac:(destruct Hq as (_ & Hq0 & _); lia) Hc1) in Qg. exact Qg.
    * apply (cno_strs_kept ly S U W mem md pos lenp _ _ ly2 S2 U W2 mem2 md2 _ HARU Hin ltac:(rewrite EFa; lia)
        ltac:(rewrite EFa; lia) ltac:(lia) HRO HJc OK2 PO2).
      intros r Hr. left. exact Hr.
- right. exists q, out. split; [exact Hb64|]. split; [exact Hq0|].
  refine (cno_dec_ret cx k ly S U W regs mem md lenp _ _ _ _ W' c' HB HS Hl1 ltac:(lia) _ HPOST).
  intros ly2 S2 W2 regs2 mem2 md2 HJc OK2 PO2 HQ. cbv beta in HQ.
  destruct HQ as (Q10 & Q4096 & Qab & Qrb & Qz & Qv & Qcs & Qg).
  pose proof (cno_dsize_pos (c_db cx)) as Hds.
  assert (Hnew : In (q - HEAD, FSH_Fn_writer.dec_size (c_db cx) + HEAD) (ablocks B ly2 S2))
    by (rewrite Qab; apply in_or_app; right; left; reflexivity).
  assert (Hrq16 : 16 <= req_size (FSH_Fn_writer.dec_size (c_db cx) + HEAD))
    by (unfold req_size, HEAD; destruct (Z.eqb_spec (FSH_Fn_writer.dec_size (c_db cx) + 16) 0); lia).
  split.
  + intros r Hr. apply in_app_or in Hr. destruct Hr as [Hr | [<- | []]].
    * destruct (Hheads r Hr) as (E16 & m' & Hm' & Hrq'). split; [exact E16|]. exists m'.
      split; [rewrite Qab; apply in_or_app; left; exact Hm' | exact Hrq'].
    * cbn [fst snd]. split; [reflexivity|]. exists (FSH_Fn_writer.dec_size (c_db cx) + HEAD).
      split; [exact Hnew | exact Hrq16].
  + split; [exact Q10|]. split; [exact Q4096|]. split; [exact Qab|]. split; [exact Qrb|]. split; [exact Qz|].
    split; [exact Qv|]. split.
    * rewrite (cno_tick cnt ltac:(destruct Hq as (_ & Hq0' & _); lia) Hc1) in Qg. exact Qg.
    * apply (cno_strs_kept ly S U W mem md pos lenp _ _ ly2 S2 _ W2 mem2 md2 _ HARU Hin ltac:(rewrite EFa; lia)
        ltac:(rewrite EFa; lia) ltac:(lia) HRO HJc OK2 PO2).
      intros r Hr. apply in_app_or in Hr. destruct Hr as [Hr | [<- | []]]; [left; exact Hr|]. right.
      intros b' m' Hbm.
      pose proof (proj1 HJc) as HAR2.
      destruct (al_blocks _ _ LAWS ly2 S2 W2 _ md2 _ _ HAR2 Hnew) as (_ & _ & _ & _ & _ & Hpw & _).
      rewrite Qab, map_app in Hpw.
      pose proof (cno_pw_last _ _ _ _ Hpw (in_map (fun b0 => (fst b0, req_size (snd b0))) _ _ Hbm)) as Hdj.
      unfold zdisjoint in Hdj. cbn [fst snd] in Hdj |- *. unfold HEAD in *. lia.
Qed.
End P.
