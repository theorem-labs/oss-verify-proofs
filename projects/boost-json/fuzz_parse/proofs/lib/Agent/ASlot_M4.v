(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A F_mm_syscalls.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_fp MallocKit_A2 AllocSlot_iface F_malloc_join Malloc_iface F_malloc_bigw F_malloc_big.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocNat MallocFacts_AS MallocKit_A3 ASlot_W0 ASlot_W1 ASlot_W9 ASlot_W10 ASlot_W11 ASlot_W14 ASlot_W15 ASlot_W16 ASlot_W17 ASlot_W18 ASlot_I ASlot_M0 ASlot_M2 ASlot_M3 ASlot_M4P.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require MallocFacts_inv4.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~04aptr37Corelib4Init5Logick42eq37Corelib4Init9Datatypesld4None04optr37Corelib7Numbers7BinNumso21Z0cget_meta_rec79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent7ASlot_I~~~~~~qd5as_kq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9ASlot_W14~~~~~~v58st_model01M06active07ag_tail08full_lay06m_next06m_prev06mstate46Stdlib6ZArith6BinInt1Zhn82lek43and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9ASlot_W16~~~~~~hpcamm_cnt_redld4bool0bround_up_pghn83addhn82lthn86modulohn83mulld4pairld4prodk42orhpc8mm_final04mctx08c_active0cc_avail_meta0h7c_avail_meta_area_count0h2c_avail_meta_areas0h2c_avail_meta_count05c_brk0h0c_free_meta_head0bc_init_done0h2c_meta_alloc_shift0h0c_meta_area_head0h0c_meta_area_tail0ec_mmap_counter08c_secret07c_usage25stdpp9countableji4bZ_countable25stdpp4gmapjk44gmap35stdpp7numbers1Zjl86eq_deck42ex0eaccount_bounce08brkstate08step_seq07upd_ctx" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Section MMEQ.
Context {R : Type}.
Variables (sc req : Z) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).

Definition mm_after (st2 : mstate) (m : aptr) (c nd : Z) : Z -> Malloc.M R :=
  let size := UNIT * size_class sc in
  let st1 := step_seq (account_bounce sc st2) in
  fun r =>
        if negb (mmap_answer_ok (live_ranges st1) nd r) then bad_answer bail else
        if is_err r then free_meta m st1 (fun st2 => as_kq sc k bail st2 None) bail
        else
          let '(st2, rid) := new_region RKGroup r nd st1 in
          let st3 := upd_meta m (m_set_maplen (Z.shiftr nd 12)) st2 in
          let st4 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st3 in
          let ai := (4096 - UNIT) / size - 1 in
          let ai := if c - 1 <? ai then c - 1 else ai in
          let ai := if ai <? 0 then 0 else ai in
          ag_tail full_lay st4 sc m (rid, 0) c ai (as_kq sc k bail).

Lemma ag_mmap_eq st2 m cnt :
  ag_mmap sc req k bail st2 m cnt =
  (let '(c, nd) := mm_final (UNIT * size_class sc) req (mm_usage1 (step_seq (account_bounce sc st2)) sc (usage st2 sc))
                              (mm_cnt_red sc (UNIT * size_class sc) cnt (mm_usage1 (step_seq (account_bounce sc st2)) sc (usage st2 sc)) (is_bouncing sc st2))
                              (is_bouncing sc st2) in
   SVis (EMmap 0 nd PROT_RW (MAP_PRIVATE + MAP_ANON)) (mm_after st2 m c nd)).
Proof. reflexivity. Qed.
End MMEQ.

Section TAILEQ.
Context {R : Type}.
Variables (sc : Z) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).
Lemma ag_tail_kq_eq : ltac2:(zQ "f0!je!l8!n5!nc!pb!pf!ud!hj7!hk2!hk5!hkd!hl6!hm0!hm8!hn0>3stT$e>2mm$0>1p$0>1c$4>2ai$4>0@3$1$3@1$c@2$5^5^4@1$2$0>0@3$1$3@1$d@2$5^6^5@1$2$0>0@3$1$3@2$9^7?2sc@1$2$0@3$1@1$8?1R@9$a?1R$b^8?2sc^7^6^5^4@4$6?1R?2sc?1k?4bail@2?1k@6$7^8?2sc^5^4^7^6Z").
Proof. intros stT mm p c ai.
  intros HN HP HA. unfold ag_tail, as_kq. cbv zeta. cbn [lh_hdr full_lay].
  rewrite as_queue_eq.
  2:{ unfold upd_meta, add_slots. rewrite get_meta_rec_put_same. cbn [m_next m_set_avail].
      rewrite rec_set_slots, rec_put_group, get_meta_rec_put_same. cbn [m_next m_prev m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail].
      rewrite rec_set_usage, rec_hdr_havoc. exact HN. }
  2:{ unfold upd_meta, add_slots. rewrite get_meta_rec_put_same. cbn [m_prev m_set_avail].
      rewrite rec_set_slots, rec_put_group, get_meta_rec_put_same. cbn [m_next m_prev m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail].
      rewrite rec_set_usage, rec_hdr_havoc. exact HP. }
  unfold as_queue_st. cbn [get_head].
  match goal with |- context [active ?X sc] => replace (active X sc) with (active stT sc) by reflexivity end.
  rewrite HA. unfold as_fm_single, st_model. cbn [set_head]. reflexivity.
Qed.
End TAILEQ.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mm_cnt_red_range : ltac2:(zQ "50!pb!hp0!hp6!hte!huc>2sc$0>4size$0>3cnt$0>2u1$0>3nos$4>0@2$2@2$1+1^3@2$1^3+i0@2$2@2$1+1@5$3^6^5^4^3^2@2$1@5$3^6^5^4^3^2+i0").
Proof. intros sc size cnt u1 nos.
  intros H. unfold mm_cnt_red.
  destruct (_ && _); [|lia]. destruct (_ && _); [lia|]. destruct (_ && _); [lia|]. destruct (_ && _); [lia|]. destruct (_ && _); lia.
Qed.

Lemma round_up_pg_props : ltac2:(zQ "80!hv3!hp6!pb!hp0!l8!ig0!ig7!igd>1x$2>0@2$3Z^1@2$1@2$1@2$3^2@1$0^2@2$6@1$0^2@2$5^2+hgg0@3$4$2@2$7@1$0^2+hgg0Z").
Proof. intros x.
  intros Hx. unfold round_up_pg. change (PGSZ - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma mm_final_props : ltac2:(zQ "d0!pb!hp0!hp6!l8!ig0!hv3!ih7!huc!ihe!ii5!iic!ij1!igd>4size$0>3req$0>2u1$0>3cnt$0>3nos$7>1c$0>2nd$0>0@2$2@2$1+1^4@2$1^4+i0>0@2$1+h0^8>0@2$1Z^8>0@2$1@2$4^9+4^a>0@3$3@2$9$0$0@5$b^b^a^9^8^7@4$8$0$0^6^5@2$2@2$2@2$1+1^7@2$1^7^9@2$2@3$3$0@2$c^6+hgg0Z@2$2@2$1@2$4^b+h4^6@2$a@2$2@3$3$0^7+1@3$3$0^6@1$5@2$4^b+h4@2$2@2$1@2$4@2$6^c^7+h0^6@3$3$0^6@1$5@2$4@2$6^c^7+h0").
Proof. intros size req u1 cnt nos c nd.
  intros HC HS HR HF E. unfold mm_final, mm_small in E. cbv zeta in E.
  pose proof (round_up_pg_props (req + 20) ltac:(lia)) as [R1 R2].
  pose proof (round_up_pg_props (size * cnt + 16) ltac:(nia)) as [N1 N2].
  change (req + IB + UNIT) with (req + 4 + 16) in E. replace (req + 4 + 16) with (req + 20) in E by lia.
  change (size * cnt + UNIT) with (size * cnt + 16) in E.
  destruct (negb nos && (cnt <=? 7)).
  - destruct (Z.ltb_spec (round_up_pg (req + 20)) (size + UNIT)) as [L|G]; cbn [orb] in E.
    + inversion E; subst. unfold UNIT in L. split; [lia|]. split; [lia|]. split; [lia|]. left; auto.
    + destruct ((4 * PGSZ <=? round_up_pg (req + 20)) && (u1 <? 2 * cnt)).
      * inversion E; subst. unfold UNIT in G. split; [lia|]. split; [lia|]. split; [lia|]. left; auto.
      * inversion E; subst. split; [lia|]. split; [lia|]. split; [nia|]. right; split; [nia| reflexivity].
  - inversion E; subst. split; [lia|]. split; [lia|]. split; [nia|]. right; split; [nia| reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stS_shape : ltac2:(zQ "hd0!l8!hp6!pb!ijd!nc!ik3!ikd!ilb!in5!ioa!ipf!iq6!ir9!is6!itb!iue!jg1!jh1!jhb!hn0!jj5!jl0!jm9!jn3!jn8!je!jo8!jp2!jpc>2sc$2>3st2$h3@2$h7>0$3$3\1f>0$3$3@2$1@3$0$h3@1$hb@2$h8^3^2@2$hc^1^2>1c$3@2$1@3$0@4$h5$2$h6$h4$h9@1$5@1^2^1@1$5^1@2$1@3$0@4$h5$2$h6$h4$2@1$h2@1^2^1@1$h2^1@2$1@3$0$ha@1$a@1^2^1@1$a^1@2$1@3$0$2@1$h0@1^2^1@1$h0^1@2$1@3$0$4@1$b@1^2^1@1$b^1@2$1@3$0$4@1$6@1^2^1@1$6^1@2$1@3$0$2@1$h1@1^2^1@1$h1^1@2$1@3$0$2@1$c@1^2^1@1$c^1@2$1@3$0$2@1$9@1^2^1@1$9^1@2$1@3$0$2@1$7@1^2^1@1$7^1@2$1@3$0$2@1$d@1^2^1@1$d^1@2$1@3$0$4@1$e@1^2^1@1$e^1@2$1@3$0$4@1$f@1^2^1@1$f^1@3$0$4@1$8@1^2^1@1$8^1").
Proof. intros sc st2.
  assert (AB : exists g, account_bounce sc st2 = upd_ctx g st2 /\ forall c, g c = c \/ exists v, g c = set_bounces_map (<[sc - 7 := v]> (c_bounces c)) c).
  { unfold account_bounce, set_bounce.
    destruct (sc_in_seq_range sc); [| exists (fun c => c); split; [destruct st2; reflexivity| intros; left; reflexivity]].
    destruct (negb _ && _); [| exists (fun c => c); split; [destruct st2; reflexivity| intros; left; reflexivity]].
    destruct (_ <? 100); (eexists; split; [reflexivity| intros c; right; eexists; reflexivity]). }
  ndestruct AB as (g & EG & HG).
  rewrite step_seq_eq. rewrite EG.
  destruct (c_seq (ctx (upd_ctx g st2)) =? 255).
  - exists (fun c => set_seq 1 (set_unmap_seq_map ∅ (g c))). split; [destruct st2; reflexivity|].
    intros c. destruct (HG c) as [E|[v E]]; rewrite E; repeat split; reflexivity.
  - exists (fun c => set_seq (c_seq (g c) + 1) (g c)). split; [destruct st2; reflexivity|].
    intros c. destruct (HG c) as [E|[v E]]; rewrite E; repeat split; reflexivity.
Qed.

Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : AREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : mrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : auxv_ok m (bv_unsigned sp).
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AS_STACK (S f).
Hypothesis ERR : rw_cells asegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv asegs m.
Hypothesis MED : rw_cells asegs m MEDTAB medtab_cells.
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  as_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  implT o (k st1 idx) s' Q ms'.
Let F0 : ISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

Variable am_pre : mstate -> Prop.
Hypothesis AM : alloc_meta_stmt am_pre.
Hypothesis AMP : AMP_AS am_pre.
End LEVEL.

End HCW.

(* [comment removed for export] *)
