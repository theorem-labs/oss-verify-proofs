(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04prod37Corelib7Numbers7BinNumshe1Nhe1Z06option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~k74aptr04bool03fst03snd04andb46Stdlib6NArith6BinNat1Nq23eqb46Stdlib6ZArith6BinInt1Zs03eqbk74optr05false04truek78aptr_eqb04pairs03addk72ev79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec5STree~~~~~~hge5streek75TWO64s03ltbs03sub04list04cons03nil37Corelib5Lists7ListDefhn93nthk7csize_classess06to_natk7dsmall_cnt_tabk7bmed_cnt_tabs06modulos03pows04lands03oppk76lowbits04log2s07testbitk74PGSZs03leb03orbk7biv_disjoint36Stdlib5Lists4Listii37forallbk7bround_up_pgk7dalloc_ceilingk7dis_errno_formk7branges_freek76shadow25stdpp9countableio6bZ_countable35stdpp7numbers1Ziq66eq_dec25stdpp4baseis15empty25stdpp4gmapit64gmapit6agmap_emptyk78mkShadowk74meta04Nonek76mkMetak74mctxk7aBrkUntriedk75mkCtxk76mstate35stdpp7numbers1Njje6eq_decio6bN_countableio6eprod_countable25stdpp9decidablejnabprod_eq_deche2N0k74areak74ghdrk76regionk74ctx0k77mkStatek77s_areask75s_ctxk78s_groupsk77s_metask7as_next_ridk79s_regionsk7as_reservedk78s_secretk78s_shadowk77s_slotsk76s_tickk78c_activek7cc_avail_metak7h7c_avail_meta_area_countk7h2c_avail_meta_areask7h2c_avail_meta_countk79c_bouncesk75c_brkk7h0c_free_meta_headk7bc_init_donek7h2c_meta_alloc_shiftk7h0c_meta_area_headk7h0c_meta_area_tailk7ec_mmap_counterk75c_seqk7bc_unmap_seqk77c_usagek78c_secretk78brkstatek73ctxis16lookupit6bgmap_lookupit6h2gmap_partial_alterk7eset_active_mapk77upd_ctxis16deleteis16insert25stdpp8fin_mapslreamap_deletelreamap_insert02id25stdpp6optionluebfrom_optionk7dset_usage_mapk7fset_bounces_mapk75meta0k79set_metask7cget_meta_reck78put_metak77m_availk7am_freeablek77m_freedk7am_last_idxk78m_maplenk75m_memk76m_nextk7bm_sizeclassk76m_prevk7cg_active_idxk79get_groupk76mkGhdrk7aset_groupsk76g_metak7aget_regionk76r_basek74conck75r_lenk75rkindk76r_kind03apphn93mapk7h1region_live_rangelrebmap_to_listit69gmap_foldk7blive_rangesk78mkRegionk7cset_next_ridk7bset_regionsq24succk7aset_shadowk74UNITk74aaddk79set_slotss04iters03mulii37existsbq23ltbk77cellval04Somek75Knownk77Unknownk75stalek78stale_pgs03divk77r_cellsk75r_havk76r_havpk77shadow0k7aget_shadowk7aupd_shadowk73wr8s06shiftr36Stdlib4Bool4Boolon47Is_trueis16filterjnabIs_true_dec35stdppblist_basics4listoqablist_filterk77hav_addk77set_seqk7h1set_unmap_seq_mapk7fsc_in_seq_rangek77bouncesk7aset_bounce04negbk79unmap_seqk7asize_classk72IBk75clz32k75lheadk76activek7aset_activek7h2set_free_meta_headk78upd_metak7am_set_nextk7am_set_prevk78optr_eqbk78set_headk78get_heads03lork7aget_stridek7bslot_start'k79small_cntk7blayout_hookk75mkLayk79hdr_havock7bnest_layout03natk7bis_bouncingk75usagek71Mk77mapinfok79free_metak76EUndefk77UBadPtrk79del_groupk79del_slotsk7arecord_seqk79set_usagek78step_seqhge4SVisk77decoderk73retk77EMunmapk74FUELk7abad_answerk73bitk7bdrop_regionk75guardk7bm_set_freedk79mask_uptok7h0munmap_answer_okk7fnontrivial_freek77testbitk78get_metak7h0get_nominal_sizek7aslot_startk74wr16k77dec_hdrk78free_hdrk79free_tailhge5sbind" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)

Local Open Scope Z_scope.
Local Open Scope stree_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition aptr : ltac2:(zQ "00T") := ltac2:(zQ "30!h8!j7!jb@2$0$1$2").          (* [comment removed for export] *)
Definition optr : ltac2:(zQ "00T") := ltac2:(zQ "20!jf!o5@1$0$1").           (* [comment removed for export] *)

Definition aptr_eqb : ltac2:(zQ "20!o5!oc>1a$0>1b$0$1") := ltac2:(zQ "80!j7!jb!p2!p7!o5!pc!ra!t8\1a$4\1b$4@2$5@2$6@3$2$0$1^2@3$2$0$1^1@2$7@3$3$0$1^2@3$3$0$1^1").
Definition optr_eqb : ltac2:(zQ "20!te!oc>1a$0>1b$0$1") := ltac2:(zQ "70!jf!o5!oc!u5!te!uc!v2\1a$4\1b$4M0\1a@1$0$1$2^2\1x$1M0\1b@1$0$1$2^2\1y$1@2$6^2^1$3M0\1b@1$0$1$2^1\2a0$1$3$5").
Definition aadd : ltac2:(zQ "20!o5!jb>1p$0>1d$1$0") := ltac2:(zQ "70!jb!j7!p2!vd!p7!o5!hg3\1p$5\1d$0@4$3$1$0@3$2$1$0^2@2$6@3$4$1$0^2^1").

Inductive undef_reason := UAssert (tag : Z) | UFuel | UBadPtr | UBadAnswer.

Inductive ev : Type :=
| EBrk (addr : Z)
| EMmap (addr len prot flags : Z)
| EMunmap (addr len : Z)
| EMprotect (addr len prot : Z)
| EPeek (p : aptr) (caddr : Z) (hint : Z)
| EUndef (why : undef_reason).

Definition M : ltac2:(zQ "00>1RTT") := ltac2:(zQ "30!jb!hg9!hkb\1RT@3$2$1$0^1").
Definition ret {R} (r : R) : M R := SRet r.

(* [comment removed for export] *)
Definition PROT_NONE : Z := 0.
Definition PROT_RW : Z := 3.          (* [comment removed for export] *)
Definition MAP_PRIVATE : Z := 2.
Definition MAP_FIXED : Z := 16.
Definition MAP_ANON : Z := 32.
Definition ENOSYS : Z := 38.
Definition TWO64 : Z := 2^64.
(* [comment removed for export] *)
Definition is_err : ltac2:(zQ "20!oc!jb>1r$1$0") := ltac2:(zQ "40!jb!hl4!hlc!hm2\1r$0@2$2@2$3$1+hgg0^1").

(* [comment removed for export] *)
Definition UNIT : Z := 16.
Definition IB : Z := 4.
Definition MMAP_THRESHOLD : Z := 131052.
Definition PGSZ : Z := 4096.   (* [comment removed for export] *)
Definition META_SIZE : Z := 40.       (* [comment removed for export] *)
Definition AREA_HDR : Z := 24.        (* [comment removed for export] *)
Definition NSLOTS : Z := 101.         (* [comment removed for export] *)

(* [comment removed for export] *)
Definition size_classes : ltac2:(zQ "20!hm8!jb@1$0$1") := ltac2:(zQ "30!jb!hme!hn4@3$1$0+1@3$1$0+2@3$1$0+3@3$1$0+4@3$1$0+5@3$1$0+6@3$1$0+7@3$1$0+8@3$1$0+9@3$1$0+a@3$1$0+c@3$1$0+f@3$1$0+h2@3$1$0+h4@3$1$0+h9@3$1$0+hf@3$1$0+i4@3$1$0+ia@3$1$0+j2@3$1$0+jf@3$1$0+k8@3$1$0+l4@3$1$0+m6@3$1$0+nf@3$1$0+p2@3$1$0+qa@3$1$0+sc@3$1$0+vf@3$1$0+hi4@3$1$0+hl4@3$1$0+hp9@3$1$0+hvf@3$1$0+ik8@3$1$0+iqa@3$1$0+jj2@3$1$0+jvf@3$1$0+kp1@3$1$0+ll4@3$1$0+mm5@3$1$0+nvf@3$1$0+pi4@3$1$0+qqa@3$1$0+ssc@3$1$0+vvf@3$1$0+hik8@3$1$0+hll4@3$1$0+hpp8@3$1$0+hvvf@1$2$0").
Definition size_class : ltac2:(zQ "10!jb>1i$0$0") := ltac2:(zQ "40!jb!hp0!hp7!hq6\1i$0@4$1$0@1$3^1$2Z").

Definition small_cnt_tab : ltac2:(zQ "20!hm8!jb@1$0@1$0$1") := ltac2:(zQ "41!jb!hme!hm8!hn4&@3$1$0+hf@3$1$0+f@3$1$0+7@1$3$0@3$1@1$2$0@3$1$0+he@3$1$0+he@3$1$0+he@1$3$0@3$1@1$2$0@3$1$0+hf@3$1$0+f@3$1$0+f@1$3$0@3$1@1$2$0@3$1$0+h4@3$1$0+a@3$1$0+a@1$3$0@3$1@1$2$0~0@3$1@1$2$0@3$1$0+h9@3$1$0+c@3$1$0+6@1$3$0@3$1@1$2$0@3$1$0+h5@3$1$0+a@3$1$0+5@1$3$0@3$1@1$2$0@3$1$0+h2@3$1$0+8@3$1$0+4@1$3$0@3$1@1$2$0~0@3$1@1$2$0@3$1$0+hc@3$1$0+e@3$1$0+6@1$3$0@1$3@1$2$0").
Definition small_cnt : ltac2:(zQ "10!jb>2sc$0>1i$0$0") := ltac2:(zQ "60!jb!hp0!hq6!hm8!hn4!hqf\2sc$0\1i$0@4$1$0@1$2^1@4$1@1$3$0@1$2^2$5@1$4$0Z").
Definition med_cnt_tab : ltac2:(zQ "20!hm8!jb@1$0$1") := ltac2:(zQ "30!jb!hme!hn4@3$1$0+hc@3$1$0+h8@3$1$0+h4@3$1$0+i0@1$2$0").
Definition med_cnt : ltac2:(zQ "10!jb>1i$0$0") := ltac2:(zQ "40!jb!hp0!hrf!hq6\1i$0@4$1$0@1$3^1$2Z").

(* [comment removed for export] *)
Definition u32 : ltac2:(zQ "10!jb>1z$0$0") := ltac2:(zQ "30!jb!hsd!ht6\1z$0@2$1^1@2$2+2+i0").
Definition bit : ltac2:(zQ "10!jb>1i$0$0") := ltac2:(zQ "20!jb!ht6\1i$0@2$1+2^1").                    (* [comment removed for export] *)
Definition mask_upto : ltac2:(zQ "10!jb>1k$0$0") := ltac2:(zQ "40!jb!hg3!ht6!hm2\1k$0@2$3@2$2+2@2$1^1+1+1").       (* [comment removed for export] *)
Definition lowbit : ltac2:(zQ "10!jb>1m$0$0") := ltac2:(zQ "30!jb!htc!hu3\1m$0@2$1^1@1$2^1").        (* [comment removed for export] *)
Definition ctz32 : ltac2:(zQ "10!jb>1m$0$0") := ltac2:(zQ "30!jb!hu9!hv2\1m$0@1$2@1$1^1").      (* [comment removed for export] *)
Definition clz32 : ltac2:(zQ "10!jb>1m$0$0") := ltac2:(zQ "30!jb!hv2!hm2\1m$0@2$2+hf@1$1^1").          (* [comment removed for export] *)
Definition testbit : ltac2:(zQ "20!jb!oc>1m$0>1i$0$1") := ltac2:(zQ "20!jb!hv9\1m$0\1i$0@2$1^2^1").

Definition round_up_pg : ltac2:(zQ "10!jb>1x$0$0") := ltac2:(zQ "60!jb!ig3!hg3!htc!hu3!hm2\1x$0@2$2^1@2$3@1$4^1@2$5$1+1").  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition alloc_ceiling : Z := 0x7fffff800000.
Definition is_errno_form : ltac2:(zQ "20!oc!jb>1r$1$0") := ltac2:(zQ "60!hl4!pc!jb!iga!hlc!hm2\1r$2@2$1@2$3@2$5$0+vvf^1@2$4^1$0").
(* [comment removed for export] *)
Definition brk0_answer_ok : ltac2:(zQ "20!oc!jb>1r$1$0") := ltac2:(zQ "70!pc!hlc!jb!ig3!hl4!t8!hsd\1r$2@2$0@2$0@2$1Z^1@2$5@2$6^1$3Z@2$1^1$4").
(* [comment removed for export] *)
Definition brk_answer_ok : ltac2:(zQ "20!jb!oc>3old$0>3new$0>1r$0$1") := ltac2:(zQ "30!jb!t8!ih0\3old$0\3new$0\1r$0@2$2@2$1^1^2@2$1^1^3").
(* [comment removed for export] *)
Definition iv_disjoint : ltac2:(zQ "20!jb!oc>1a$0>1n$0>1b$0>1m$0$1") := ltac2:(zQ "40!jb!hg3!iga!ih0\1a$0\1n$0\1b$0\1m$0@2$3@2$2@2$1^4^3^2@2$2@2$1^2^1^4").
Definition ranges_free : ltac2:(zQ "40!jb!oc!hm8!h8>1l@1$2@2$3$0$0>1a$0>1n$0$1") := ltac2:(zQ "70!jb!h8!p2!hm8!p7!ih5!ij6\1l@1$3@2$1$0$0\1a$0\1n$0@3$6@2$1$0$0\2bm@2$1$0$0@4$5^3^2@3$2$0$0^1@3$4$0$0^1^3").
(* [comment removed for export] *)
Definition mmap_answer_ok : ltac2:(zQ "40!jb!oc!hm8!h8>4live@1$2@2$3$0$0>3len$0>1r$0$1") := ltac2:(zQ "f0!jb!pc!ik1!hm8!ih0!h8!ig3!ikf!ilf!imf!hg3!t8!iga!hlc!hsd\4live@1$3@2$5$0$0\3len$0\1r$0@2$4@1$8^1@2$1@2$1@2$1@2$dZ^1@2$b@2$e^1$6Z@2$c@2$a^1@1$2^2$7@3$9^3^1@1$2^2").
(* [comment removed for export] *)
Definition mmap_fixed_answer_ok : ltac2:(zQ "20!jb!oc>1a$0>1r$0$1") := ltac2:(zQ "40!jb!ih0!ilf!t8\1a$0\1r$0@2$1@1$2^1@2$3^1^2").
(* [comment removed for export] *)
Definition munmap_answer_ok : ltac2:(zQ "20!oc!jb>1r$1$0") := ltac2:(zQ "40!ih0!jb!ilf!t8\1r$1@2$0@2$3^1Z@1$2^1").
Definition mprotect_answer_ok : ltac2:(zQ "20!oc!jb>1r$1$0") := ltac2:(zQ "40!ih0!jb!ilf!t8\1r$1@2$0@2$3^1Z@1$2^1").
Definition peek_answer_ok : ltac2:(zQ "20!oc!jb>1r$1$0") := ltac2:(zQ "40!pc!jb!iga!hlc\1r$1@2$0@2$2Z^1@2$3^1+hg0").

(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive rkind := RKBrk | RKMeta | RKGroup.

Record region := mkRegion {
  r_kind  : rkind;
  r_base  : Z;                 (* [comment removed for export] *)
  r_len   : Z                  (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Record shadow := mkShadow {
  r_cells : gmap Z (Z * N);    (* [comment removed for export] *)
  r_hav   : gmap Z (list (Z * N)); (* [comment removed for export] *)
  r_havp  : gmap Z N           (* [comment removed for export] *)
}.
Definition shadow0 : ltac2:(zQ "10!ind$0") := ltac2:(zQ "a0!jb!j7!ip7!ir7!h8!isd!iu2!iua!hm8!iv8@3$9@2$5@4$6$0$3$2@2$4$0$1@4$7$0$3$2@2$4$0$1@2$5@4$6$0$3$2@1$8@2$4$0$1@4$7$0$3$2@1$8@2$4$0$1@2$5@4$6$0$3$2$1@4$7$0$3$2$1").

(* [comment removed for export] *)
Record meta := mkMeta {
  m_prev : optr; m_next : optr; m_mem : optr;
  m_avail : Z; m_freed : Z;
  m_last_idx : Z; m_freeable : Z; m_sizeclass : Z; m_maplen : Z
}.
Definition meta0 : ltac2:(zQ "10!jg3$0") := ltac2:(zQ "30!jga!o5!jh0@9$2@1$0$1@1$0$1@1$0$1ZZZZZZ").

(* [comment removed for export] *)
Record area := mkArea { a_check : Z; a_next : optr; a_nslots : Z }.

(* [comment removed for export] *)
Record ghdr := mkGhdr { g_meta : optr; g_active_idx : Z }.

(* [comment removed for export] *)
Inductive brkstate := BrkUntried | BrkDead | BrkLive (rid : N) (off : Z).

(* [comment removed for export] *)
Record mctx := mkCtx {
  c_secret : Z;
  c_init_done : Z;
  c_mmap_counter : Z;          (* [comment removed for export] *)
  c_free_meta_head : optr;
  c_avail_meta : optr;
  c_avail_meta_count : Z;
  c_avail_meta_area_count : Z;
  c_meta_alloc_shift : Z;
  c_meta_area_head : optr;
  c_meta_area_tail : optr;
  c_avail_meta_areas : optr;
  c_active : gmap Z aptr;      (* [comment removed for export] *)
  c_usage : gmap Z Z;          (* [comment removed for export] *)
  c_unmap_seq : gmap Z Z;      (* [comment removed for export] *)
  c_bounces : gmap Z Z;        (* [comment removed for export] *)
  c_seq : Z;                   (* [comment removed for export] *)
  c_brk : brkstate
}.
Definition ctx0 : ltac2:(zQ "10!jh9$0") := ltac2:(zQ "a1!jb!ip7!ir7!o5!jga!isd!iu2!iua!ji0!jid&@2$5@4$6$0$2$1$0@4$7$0$2$1$0@h1$9ZZZ@1$4$3@1$4$3ZZZ@1$4$3@1$4$3@1$4$3@2$5@4$6$0$2$1$3@4$7$0$2$1$3~0~0~0Z$8").

Record mstate := mkState {
  s_ctx : mctx;
  s_regions : gmap N region;
  s_shadow : gmap N shadow;       (* [comment removed for export] *)
  s_next_rid : N;
  s_metas : gmap aptr meta;
  s_areas : gmap aptr area;
  s_groups : gmap aptr ghdr;
  s_slots : gmap aptr (aptr * Z); (* [comment removed for export] *)
  s_tick : N;
  s_secret : Z;                (* [comment removed for export] *)
  s_reserved : list (Z * Z)    (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition minit : ltac2:(zQ "40!jb!hm8!h8!jj5>6secret$0>8reserved@1$1@2$2$0$0$3") := ltac2:(zQ "h60!jb!j7!jkf!ir7!jl9!o5!ip7!jm8!job!isd!iu2!iua!h8!jpa!jpf!jq6!jg3!jqd!ind!hm8!jr6!jrd\6secret$0\8reserved@1$h3@2$c$0$0@b$h5$h4@2$9@4$a$1$2$4$h1@4$b$1$2$4$h1@2$9@4$a$1$2$4$h2@4$b$1$2$4$h2$d@2$9@4$a$5@4$8$1$2$0$3@6$7$1$2$4$0$3$6$h0@4$b$5@4$8$1$2$0$3@6$7$1$2$4$0$3$6$h0@2$9@4$a$5@4$8$1$2$0$3@6$7$1$2$4$0$3$6$e@4$b$5@4$8$1$2$0$3@6$7$1$2$4$0$3$6$e@2$9@4$a$5@4$8$1$2$0$3@6$7$1$2$4$0$3$6$f@4$b$5@4$8$1$2$0$3@6$7$1$2$4$0$3$6$f@2$9@4$a$5@4$8$1$2$0$3@6$7$1$2$4$0$3$6@2$c$5$0@4$b$5@4$8$1$2$0$3@6$7$1$2$4$0$3$6@2$c$5$0$d^2^1").

(* [comment removed for export] *)
Definition upd_ctx : ltac2:(zQ "20!jh9!jj5>1f>0$0$0>2st$1$1") := ltac2:(zQ "e0!jh9!jrd!jj5!js7!jt1!jt9!ju4!jue!jvb!kg7!kh4!khf!kia!kj4\1f>0$0$0\2st$2@b$1@1^2@1$4^1@1$8^1@1$b^1@1$7^1@1$6^1@1$3^1@1$5^1@1$c^1@1$d^1@1$a^1@1$9^1").
Definition set_regions : ltac2:(zQ "60!jj5!j7!jqd!jl9!iu2!jkf>1v@4$4$1$5$3$2>2st$0$0") := ltac2:(zQ "h10!j7!jrd!jj5!jqd!js7!jt1!jt9!ju4!jue!kg7!kh4!khf!kia!kj4!jl9!iu2!jkf\1v@4$f$0$h0$e$3\2st$2@b$1@1$5^1^2@1$b^1@1$8^1@1$7^1@1$4^1@1$6^1@1$c^1@1$d^1@1$a^1@1$9^1").
Definition set_shadow : ltac2:(zQ "60!jj5!j7!ind!jl9!iu2!jkf>1v@4$4$1$5$3$2>2st$0$0") := ltac2:(zQ "h10!j7!jrd!jj5!js7!jt1!jt9!ju4!jue!jvb!kg7!kh4!kia!kj4!ind!jl9!iu2!jkf\1v@4$f$0$h0$e$d\2st$2@b$1@1$4^1@1$8^1^2@1$7^1@1$6^1@1$3^1@1$5^1@1$b^1@1$c^1@1$a^1@1$9^1").
Definition set_next_rid : ltac2:(zQ "20!jj5!j7>1v$1>2st$0$0") := ltac2:(zQ "d0!j7!jrd!jj5!js7!jt1!jt9!ju4!jvb!kg7!kh4!khf!kia!kj4\1v$0\2st$2@b$1@1$4^1@1$7^1@1$a^1^2@1$6^1@1$3^1@1$5^1@1$b^1@1$c^1@1$9^1@1$8^1").
Definition set_metas : ltac2:(zQ "c0!j7!jb!jj5!jkf!ir7!o5!jg3!jl9!ip7!jm8!job!iu2>1v@4$b$5@4$a$0$3$1$4@6$9$0$3$7$1$4$8$6>2st$2$2") := ltac2:(zQ "h70!j7!jb!jkf!ir7!o5!jg3!jrd!jj5!js7!jt1!jt9!jue!jvb!kg7!kh4!khf!kia!kj4!jl9!ip7!jm8!job!iu2\1v@4$h6$4@4$h5$0$2$1$3@6$h4$0$2$h2$1$3$h3$5\2st$7@b$6@1$9^1@1$c^1@1$f^1@1$b^1^2@1$8^1@1$a^1@1$h0^1@1$h1^1@1$e^1@1$d^1").
Definition set_areas : ltac2:(zQ "c0!j7!jb!jj5!jkf!ir7!o5!jpf!jl9!ip7!jm8!job!iu2>1v@4$b$5@4$a$0$3$1$4@6$9$0$3$7$1$4$8$6>2st$2$2") := ltac2:(zQ "h70!j7!jb!jkf!ir7!o5!jpf!jrd!jj5!jt1!jt9!ju4!jue!jvb!kg7!kh4!khf!kia!kj4!jl9!ip7!jm8!job!iu2\1v@4$h6$4@4$h5$0$2$1$3@6$h4$0$2$h2$1$3$h3$5\2st$7@b$6@1$8^1@1$c^1@1$f^1@1$b^1@1$a^1^2@1$9^1@1$h0^1@1$h1^1@1$e^1@1$d^1").
Definition set_groups : ltac2:(zQ "c0!j7!jb!jj5!jkf!ir7!o5!jq6!jl9!ip7!jm8!job!iu2>1v@4$b$5@4$a$0$3$1$4@6$9$0$3$7$1$4$8$6>2st$2$2") := ltac2:(zQ "h70!j7!jb!jkf!ir7!o5!jq6!jrd!jj5!js7!jt1!ju4!jue!jvb!kg7!kh4!khf!kia!kj4!jl9!ip7!jm8!job!iu2\1v@4$h6$4@4$h5$0$2$1$3@6$h4$0$2$h2$1$3$h3$5\2st$7@b$6@1$9^1@1$c^1@1$f^1@1$b^1@1$a^1@1$8^1^2@1$h0^1@1$h1^1@1$e^1@1$d^1").
Definition set_slots : ltac2:(zQ "c0!jb!j7!o5!jj5!jkf!ir7!h8!jl9!ip7!jm8!job!iu2>1v@4$b$2@4$a$1$4$0$5@6$9$1$4$7$0$5$8@2$6$2$0>2st$3$3") := ltac2:(zQ "h70!jb!j7!o5!jkf!ir7!h8!jrd!jj5!js7!jt1!jt9!ju4!jue!jvb!kg7!kh4!khf!kj4!jl9!ip7!jm8!job!iu2\1v@4$h6$2@4$h5$1$3$0$4@6$h4$1$3$h2$0$4$h3@2$5$2$0\2st$7@b$6@1$9^1@1$d^1@1$h0^1@1$c^1@1$b^1@1$8^1@1$a^1^2@1$h1^1@1$f^1@1$e^1").
Definition set_tick : ltac2:(zQ "20!jj5!j7>1v$1>2st$0$0") := ltac2:(zQ "d0!j7!jrd!jj5!js7!jt1!jt9!ju4!jue!jvb!kg7!kh4!khf!kia\1v$0\2st$2@b$1@1$4^1@1$8^1@1$b^1@1$7^1@1$6^1@1$3^1@1$5^1@1$c^1^2@1$a^1@1$9^1").

Definition set_secret : ltac2:(zQ "20!jh9!jb>1v$1>1c$0$0") := ltac2:(zQ "h30!jb!kjd!kk8!kl7!kn2!ko8!kpe!kqa!kr2!ks6!kt4!kua!kve!lh2!li3!lib!lj9!jh9!jid\1v$0\1c$h1@h1$h2^2@1$9^1@1$d^1@1$8^1@1$2^1@1$5^1@1$3^1@1$a^1@1$b^1@1$c^1@1$4^1@1$1^1@1$h0^1@1$f^1@1$6^1@1$e^1@1$7^1").
Definition set_init_done : ltac2:(zQ "20!jh9!jb>1v$1>1c$0$0") := ltac2:(zQ "h30!jb!kjd!kk8!kl7!kn2!ko8!kpe!kqa!kr2!kt4!kua!kve!lh2!lk3!li3!lib!lj9!jh9!jid\1v$0\1c$h1@h1$h2@1$d^1^2@1$c^1@1$8^1@1$2^1@1$5^1@1$3^1@1$9^1@1$a^1@1$b^1@1$4^1@1$1^1@1$h0^1@1$f^1@1$6^1@1$e^1@1$7^1").
Definition set_mmap_counter : ltac2:(zQ "20!jh9!jb>1v$1>1c$0$0") := ltac2:(zQ "h30!jb!kjd!kk8!kl7!kn2!ko8!kpe!kqa!kr2!ks6!kt4!kua!kve!lk3!li3!lib!lj9!jh9!jid\1v$0\1c$h1@h1$h2@1$d^1@1$9^1^2@1$8^1@1$2^1@1$5^1@1$3^1@1$a^1@1$b^1@1$c^1@1$4^1@1$1^1@1$h0^1@1$f^1@1$6^1@1$e^1@1$7^1").
Definition set_free_meta_head : ltac2:(zQ "20!jh9!te>1v$1>1c$0$0") := ltac2:(zQ "h30!kjd!kk8!kl7!kn2!ko8!kpe!kqa!ks6!kt4!kua!kve!lh2!lk3!li3!lib!lj9!jh9!jid!te\1v$h2\1c$h0@h1$h1@1$c^1@1$7^1@1$b^1^2@1$1^1@1$4^1@1$2^1@1$8^1@1$9^1@1$a^1@1$3^1@1$0^1@1$f^1@1$e^1@1$5^1@1$d^1@1$6^1").
Definition set_avail_meta : ltac2:(zQ "20!jh9!te>1v$1>1c$0$0") := ltac2:(zQ "h30!kjd!kl7!kn2!ko8!kpe!kqa!kr2!ks6!kt4!kua!kve!lh2!lk3!li3!lib!lj9!jh9!jid!te\1v$h2\1c$h0@h1$h1@1$c^1@1$7^1@1$b^1@1$6^1^2@1$3^1@1$1^1@1$8^1@1$9^1@1$a^1@1$2^1@1$0^1@1$f^1@1$e^1@1$4^1@1$d^1@1$5^1").
Definition set_avail_meta_count : ltac2:(zQ "20!jh9!jb>1v$1>1c$0$0") := ltac2:(zQ "h30!jb!kjd!kk8!kl7!kn2!kpe!kqa!kr2!ks6!kt4!kua!kve!lh2!lk3!li3!lib!lj9!jh9!jid\1v$0\1c$h1@h1$h2@1$d^1@1$8^1@1$c^1@1$7^1@1$2^1^2@1$3^1@1$9^1@1$a^1@1$b^1@1$4^1@1$1^1@1$h0^1@1$f^1@1$5^1@1$e^1@1$6^1").
Definition set_avail_meta_area_count : ltac2:(zQ "20!jh9!jb>1v$1>1c$0$0") := ltac2:(zQ "h30!jb!kjd!kk8!kn2!ko8!kpe!kqa!kr2!ks6!kt4!kua!kve!lh2!lk3!li3!lib!lj9!jh9!jid\1v$0\1c$h1@h1$h2@1$d^1@1$8^1@1$c^1@1$7^1@1$2^1@1$4^1^2@1$9^1@1$a^1@1$b^1@1$3^1@1$1^1@1$h0^1@1$f^1@1$5^1@1$e^1@1$6^1").
Definition set_meta_alloc_shift : ltac2:(zQ "20!jh9!jb>1v$1>1c$0$0") := ltac2:(zQ "h30!jb!kjd!kk8!kl7!kn2!ko8!kpe!kqa!kr2!ks6!kua!kve!lh2!lk3!li3!lib!lj9!jh9!jid\1v$0\1c$h1@h1$h2@1$d^1@1$9^1@1$c^1@1$8^1@1$2^1@1$5^1@1$3^1^2@1$a^1@1$b^1@1$4^1@1$1^1@1$h0^1@1$f^1@1$6^1@1$e^1@1$7^1").
Definition set_meta_area_head : ltac2:(zQ "20!jh9!te>1v$1>1c$0$0") := ltac2:(zQ "h30!kjd!kk8!kl7!kn2!ko8!kpe!kqa!kr2!ks6!kt4!kve!lh2!lk3!li3!lib!lj9!jh9!jid!te\1v$h2\1c$h0@h1$h1@1$c^1@1$8^1@1$b^1@1$7^1@1$1^1@1$4^1@1$2^1@1$9^1^2@1$a^1@1$3^1@1$0^1@1$f^1@1$e^1@1$5^1@1$d^1@1$6^1").
Definition set_meta_area_tail : ltac2:(zQ "20!jh9!te>1v$1>1c$0$0") := ltac2:(zQ "h30!kjd!kk8!kl7!kn2!ko8!kpe!kqa!kr2!ks6!kt4!kua!lh2!lk3!li3!lib!lj9!jh9!jid!te\1v$h2\1c$h0@h1$h1@1$c^1@1$8^1@1$b^1@1$7^1@1$1^1@1$4^1@1$2^1@1$9^1@1$a^1^2@1$3^1@1$0^1@1$f^1@1$e^1@1$5^1@1$d^1@1$6^1").
Definition set_avail_meta_areas : ltac2:(zQ "20!jh9!te>1v$1>1c$0$0") := ltac2:(zQ "h30!kjd!kk8!kl7!ko8!kpe!kqa!kr2!ks6!kt4!kua!kve!lh2!lk3!li3!lib!lj9!jh9!jid!te\1v$h2\1c$h0@h1$h1@1$c^1@1$7^1@1$b^1@1$6^1@1$1^1@1$3^1@1$2^1@1$8^1@1$9^1@1$a^1^2@1$0^1@1$f^1@1$e^1@1$4^1@1$d^1@1$5^1").
Definition set_active_map : ltac2:(zQ "60!jh9!jb!o5!ip7!iu2!ir7>1v@4$4$1$5$3$2>1c$0$0") := ltac2:(zQ "h70!jb!o5!kk8!kl7!kn2!ko8!kpe!kqa!kr2!ks6!kt4!kua!kve!lh2!lk3!li3!lib!lj9!jh9!jid!ip7!iu2!ir7\1v@4$h5$0$h6$h4$1\1c$h2@h1$h3@1$e^1@1$9^1@1$d^1@1$8^1@1$2^1@1$5^1@1$3^1@1$a^1@1$b^1@1$c^1@1$4^1^2@1$h1^1@1$h0^1@1$6^1@1$f^1@1$7^1").
Definition set_usage_map : ltac2:(zQ "50!jb!jh9!ip7!iu2!ir7>1v@4$3$0$4$2$0>1c$1$1") := ltac2:(zQ "h60!jb!kjd!kk8!kl7!kn2!ko8!kpe!kqa!kr2!ks6!kt4!kua!kve!lh2!lk3!li3!lib!jh9!jid!ip7!iu2!ir7\1v@4$h4$0$h5$h3$0\1c$h1@h1$h2@1$e^1@1$9^1@1$d^1@1$8^1@1$2^1@1$5^1@1$3^1@1$a^1@1$b^1@1$c^1@1$4^1@1$1^1^2@1$h0^1@1$6^1@1$f^1@1$7^1").
Definition set_unmap_seq_map : ltac2:(zQ "50!jb!jh9!ip7!iu2!ir7>1v@4$3$0$4$2$0>1c$1$1") := ltac2:(zQ "h60!jb!kjd!kk8!kl7!kn2!ko8!kpe!kqa!kr2!ks6!kt4!kua!kve!lh2!lk3!li3!lj9!jh9!jid!ip7!iu2!ir7\1v@4$h4$0$h5$h3$0\1c$h1@h1$h2@1$e^1@1$9^1@1$d^1@1$8^1@1$2^1@1$5^1@1$3^1@1$a^1@1$b^1@1$c^1@1$4^1@1$1^1@1$h0^1^2@1$6^1@1$f^1@1$7^1").
Definition set_bounces_map : ltac2:(zQ "50!jb!jh9!ip7!iu2!ir7>1v@4$3$0$4$2$0>1c$1$1") := ltac2:(zQ "h60!jb!kjd!kk8!kl7!kn2!ko8!kqa!kr2!ks6!kt4!kua!kve!lh2!lk3!li3!lib!lj9!jh9!jid!ip7!iu2!ir7\1v@4$h4$0$h5$h3$0\1c$h1@h1$h2@1$d^1@1$8^1@1$c^1@1$7^1@1$2^1@1$5^1@1$3^1@1$9^1@1$a^1@1$b^1@1$4^1@1$1^1@1$h0^1@1$f^1^2@1$e^1@1$6^1").
Definition set_seq : ltac2:(zQ "20!jh9!jb>1v$1>1c$0$0") := ltac2:(zQ "h30!jb!kjd!kk8!kl7!kn2!ko8!kpe!kqa!kr2!ks6!kt4!kua!kve!lh2!lk3!lib!lj9!jh9!jid\1v$0\1c$h1@h1$h2@1$e^1@1$9^1@1$d^1@1$8^1@1$2^1@1$5^1@1$3^1@1$a^1@1$b^1@1$c^1@1$4^1@1$1^1@1$h0^1@1$f^1@1$6^1^2@1$7^1").
Definition set_brk : ltac2:(zQ "20!jh9!lke>1v$1>1c$0$0") := ltac2:(zQ "h30!lke!kjd!kk8!kl7!kn2!ko8!kpe!kr2!ks6!kt4!kua!kve!lh2!lk3!li3!lib!lj9!jh9!jid\1v$0\1c$h1@h1$h2@1$d^1@1$8^1@1$c^1@1$7^1@1$2^1@1$5^1@1$3^1@1$9^1@1$a^1@1$b^1@1$4^1@1$1^1@1$h0^1@1$f^1@1$6^1@1$e^1^2").

Definition ctx : ltac2:(zQ "20!jh9!jj5>2st$1$0") := ltac2:(zQ "20!jj5!jt1\2st$0@1$1^1").

(* [comment removed for export] *)
Definition active : ltac2:(zQ "30!jb!jj5!te>2st$1>2sc$0$2") := ltac2:(zQ "a0!jb!o5!ip7!ir7!kjd!ll9!jj5!llf!iu2!lm9\2st$6\2sc$0@6$7$0$1@4$8$0$3$2$1@4$9$0$3$2$1^1@1$4@1$5^2").
Definition set_active : ltac2:(zQ "30!jj5!jb!te>2sc$1>1v$2>2st$0$0") := ltac2:(zQ "h10!jb!o5!ip7!ir7!iu2!jf!kjd!ln8!jh9!jj5!te!lof!lq0!lqa!lr4!lse!ltc\2sc$0\1v$a\2st$9@2$c\1c$8@2$bM5\1v@1$5$1@4$4$0$3$2$1^3\1p$1@7$e$0$1@4$4$0$3$2$1@4$h0$0$1@4$4$0$3$2$1@4$7$0$3$2$1^5^1@1$6^2@5$d$0@4$4$0$3$2$1@4$f$0$1@4$4$0$3$2$1@4$7$0$3$2$1^4@1$6^1^1^1").
Definition usage : ltac2:(zQ "20!jb!jj5>2st$1>2sc$0$0") := ltac2:(zQ "b0!jb!ip7!ir7!lua!lj9!ll9!jj5!llf!iu2!lm9!lvc\2st$6\2sc$0@5$a$0$0@1$3$0Z@6$7$0$0@4$8$0$2$1$0@4$9$0$2$1$0^1@1$4@1$5^2").
Definition set_usage : ltac2:(zQ "20!jb!jj5>2sc$0>1v$0>2st$1$1") := ltac2:(zQ "c0!jb!ip7!ir7!iu2!lj9!jh9!jj5!mgb!lq0!lr4!ltc!ln8\2sc$0\1v$0\2st$6@2$8\1c$5@2$7@7$9$0$0@4$3$0$2$1$0@4$a$0$0@4$3$0$2$1$0@4$b$0$2$1$0^4^3@1$4^1^1^1").
Definition unmap_seq : ltac2:(zQ "20!jb!jj5>2st$1>1i$0$0") := ltac2:(zQ "b0!jb!ip7!ir7!lua!lib!ll9!jj5!llf!iu2!lm9!lvc\2st$6\1i$0@5$a$0$0@1$3$0Z@6$7$0$0@4$8$0$2$1$0@4$9$0$2$1$0^1@1$4@1$5^2").
Definition bounces : ltac2:(zQ "20!jb!jj5>2st$1>1i$0$0") := ltac2:(zQ "b0!jb!ip7!ir7!lua!kpe!ll9!jj5!llf!iu2!lm9!lvc\2st$6\1i$0@5$a$0$0@1$3$0Z@6$7$0$0@4$8$0$2$1$0@4$9$0$2$1$0^1@1$4@1$5^2").
Definition set_bounce : ltac2:(zQ "20!jb!jj5>1i$0>1v$0>2st$1$1") := ltac2:(zQ "c0!jb!ip7!ir7!iu2!kpe!jh9!jj5!mhb!lq0!lr4!ltc!ln8\1i$0\1v$0\2st$6@2$8\1c$5@2$7@7$9$0$0@4$3$0$2$1$0@4$a$0$0@4$3$0$2$1$0@4$b$0$2$1$0^4^3@1$4^1^1^1").

(* [comment removed for export] *)
Definition get_meta_rec : ltac2:(zQ "30!o5!jg3!jj5>2st$2>1m$0$1") := ltac2:(zQ "h20!jg3!j7!jb!o5!jkf!ir7!jl9!ip7!jm8!job!lua!mid!jj5!ju4!llf!iu2!lm9!lvc\2st$c\1m$3@5$h1$0$0@1$a$0$b@6$e$3$0@4$f$3@4$9$1$4$2$5@6$8$1$4$6$2$5$7$0@4$h0$3@4$9$1$4$2$5@6$8$1$4$6$2$5$7$0^1@1$d^2").
Definition put_meta : ltac2:(zQ "30!jj5!o5!jg3>1m$1>1r$2>2st$0$0") := ltac2:(zQ "h11!j7!jb!o5!jg3!jkf!ir7!jl9!ip7!jm8!job!iu2!jj5!ju4!mj5!lr4!ltc!ln8&@4$a$2@4$9$0$4$1$5@6$8$0$4$6$1$5$7$3\1m$2\1r$3\2st$b@2$d@7$e$2$3~0@4$f$2$3~0@4$h0$2@4$9$0$4$1$5@6$8$0$4$6$1$5$7$3^3^2@1$c^1^1").
Definition upd_meta : ltac2:(zQ "30!jg3!jj5!o5>1m$2>1f>0$0$0>2st$1$1") := ltac2:(zQ "50!jg3!o5!mk1!jj5!ml0\1m$1\1f>0$0$0\2st$3@3$4^3@1^2@2$2^1^3^1").
Definition m_set_prev : ltac2:(zQ "20!jg3!te>1v$1>1r$0$0") := ltac2:(zQ "b0!mlb!mm5!mn2!mnc!mo9!mp4!mpc!mq5!jg3!jh0!te\1v$a\1r$8@9$9^2@1$6^1@1$5^1@1$0^1@1$2^1@1$3^1@1$1^1@1$7^1@1$4^1").
Definition m_set_next : ltac2:(zQ "20!jg3!te>1v$1>1r$0$0") := ltac2:(zQ "b0!mlb!mm5!mn2!mnc!mo9!mp4!mr3!mq5!jg3!jh0!te\1v$a\1r$8@9$9@1$6^1^2@1$5^1@1$0^1@1$2^1@1$3^1@1$1^1@1$7^1@1$4^1").
Definition m_set_mem : ltac2:(zQ "20!jg3!te>1v$1>1r$0$0") := ltac2:(zQ "b0!mlb!mm5!mn2!mnc!mo9!mpc!mr3!mq5!jg3!jh0!te\1v$a\1r$8@9$9@1$6^1@1$5^1^2@1$0^1@1$2^1@1$3^1@1$1^1@1$7^1@1$4^1").
Definition m_set_avail : ltac2:(zQ "20!jg3!jb>1v$1>1r$0$0") := ltac2:(zQ "b0!jb!mm5!mn2!mnc!mo9!mp4!mpc!mr3!mq5!jg3!jh0\1v$0\1r$9@9$a@1$7^1@1$6^1@1$5^1^2@1$2^1@1$3^1@1$1^1@1$8^1@1$4^1").
Definition m_set_freed : ltac2:(zQ "20!jg3!jb>1v$1>1r$0$0") := ltac2:(zQ "b0!jb!mlb!mm5!mnc!mo9!mp4!mpc!mr3!mq5!jg3!jh0\1v$0\1r$9@9$a@1$7^1@1$6^1@1$5^1@1$1^1^2@1$3^1@1$2^1@1$8^1@1$4^1").
Definition m_set_last_idx : ltac2:(zQ "20!jg3!jb>1v$1>1r$0$0") := ltac2:(zQ "c0!jb!mlb!mm5!mn2!mo9!mp4!mpc!mr3!mq5!jg3!jh0!htc\1v$0\1r$9@9$a@1$7^1@1$6^1@1$5^1@1$1^1@1$3^1@2$b^2+hf@1$2^1@1$8^1@1$4^1").
Definition m_set_freeable : ltac2:(zQ "20!jg3!jb>1v$1>1r$0$0") := ltac2:(zQ "c0!jb!mlb!mn2!mnc!mo9!mp4!mpc!mr3!mq5!jg3!jh0!htc\1v$0\1r$9@9$a@1$7^1@1$6^1@1$5^1@1$1^1@1$2^1@1$3^1@2$b^2+1@1$8^1@1$4^1").
Definition m_set_sizeclass : ltac2:(zQ "20!jg3!jb>1v$1>1r$0$0") := ltac2:(zQ "c0!jb!mlb!mm5!mn2!mnc!mo9!mp4!mpc!mr3!jg3!jh0!htc\1v$0\1r$9@9$a@1$8^1@1$7^1@1$6^1@1$1^1@1$3^1@1$4^1@1$2^1@2$b^2+jf@1$5^1").
Definition m_set_maplen : ltac2:(zQ "20!jg3!jb>1v$1>1r$0$0") := ltac2:(zQ "e0!jb!mlb!mm5!mn2!mnc!mp4!mpc!mr3!mq5!jg3!jh0!htc!ht6!hm2\1v$0\1r$9@9$a@1$7^1@1$6^1@1$5^1@1$1^1@1$3^1@1$4^1@1$2^1@1$8^1@2$b^2@2$d@2$c+2+j4+1").

(* [comment removed for export] *)
Definition get_group : ltac2:(zQ "40!jf!o5!jq6!jj5>2st$3>1g$1@1$0$2") := ltac2:(zQ "f0!j7!jb!o5!jkf!ir7!jq6!jl9!ip7!jm8!job!jj5!jt9!llf!iu2!lm9\2st$a\1g$2@6$c$2$5@4$d$2@4$9$0$3$1$4@6$8$0$3$6$1$4$7$5@4$e$2@4$9$0$3$1$4@6$8$0$3$6$1$4$7$5^1@1$b^2").
Definition group_active_idx : ltac2:(zQ "30!jb!o5!jj5>2st$2>1g$1$0") := ltac2:(zQ "80!jf!jq6!jb!o5!mrc!msb!jj5!htc\2st$6\1g$3M0\1x@1$0$1$2@2$5^2^1\1h$1@2$7@1$4^1+hfZ").
(* [comment removed for export] *)
Definition put_group : ltac2:(zQ "40!jj5!jb!o5!te>1g$2>1m$3>2ai$1>2st$0$0") := ltac2:(zQ "h41!jb!j7!o5!jkf!ir7!jq6!jl9!ip7!jm8!job!iu2!mt7!jj5!te!jt9!mu0!htc!lr4!ltc!ln8&@4$a$2@4$9$1$3$0$4@6$8$1$3$6$0$4$7$5\1g$2\1m$d\2ai$0\2st$c@2$f@7$h1$2$5~0@4$h2$2$5~0@4$h3$2@4$9$1$3$0$4@6$8$1$3$6$0$4$7$5^4@2$b^3@2$h0^2+hf@1$e^1^1").
(* [comment removed for export] *)
Definition set_group_active_idx : ltac2:(zQ "30!jj5!jb!o5>1g$2>2ai$1>2st$0$0") := ltac2:(zQ "h61!jb!jq6!j7!o5!jkf!ir7!jl9!ip7!jm8!job!jf!jj5!iu2!mud!msb!mt7!jt9!mu0!htc!lr4!ltc!ln8&@4$c$3@4$9$2$4$0$5@6$8$2$4$6$0$5$7$1\1g$3\2ai$0\2st$bMa\1x@1$a$1$b@2$e^1^3\1h$1@2$h1@7$h3$3$1~0@4$h4$3$1~0@4$h5$3@4$9$2$4$0$5@6$8$2$4$6$0$5$7$1^4@2$f@1$d^1@2$h2^3+hf@1$h0^2^2^1").

(* [comment removed for export] *)
Definition get_region : ltac2:(zQ "40!jf!j7!jj5!jqd>2st$2>3rid$1@1$0$3") := ltac2:(zQ "90!j7!jqd!jl9!jkf!jj5!jvb!llf!iu2!lm9\2st$4\3rid$0@6$6$0$1@4$7$0$3$2$1@4$8$0$3$2$1^1@1$5^2").
Definition conc : ltac2:(zQ "30!jb!o5!jj5>2st$2>1p$1$0") := ltac2:(zQ "b0!jb!jf!j7!jqd!p2!p7!o5!mv6!jj5!ng3!hg3\2st$8\1p$6M1\1x@1$1$3$0@2$7^2@3$4$2$0^1\1r$3@2$a@1$9^1@3$5$2$0^2Z").
Definition oconc : ltac2:(zQ "30!jb!jj5!te>2st$1>1p$2$0") := ltac2:(zQ "60!jf!o5!jb!ngc!jj5!te\2st$4\1p$5M0\1p@1$0$1$2^1\1q$1@2$3^3^1Z").
(* [comment removed for export] *)
Definition region_live_range : ltac2:(zQ "30!jb!h8!jqd>1r$2@2$1$0$0") := ltac2:(zQ "c1!jb!vd!ng3!nh3!ik1!ig3!nhb!h8!ni3!jqd!hg3!hm2&@4$1$0$0@1$2^1@1$4@1$3^1\1r$9M6\1x$6@2$7$0$0@1$8^1@4$1$0$0@2$a@1$2^1$5@2$b@1$4@1$3^1$5~0~0").
Definition live_ranges : ltac2:(zQ "40!jb!hm8!h8!jj5>2st$3@1$1@2$2$0$0") := ltac2:(zQ "h00!j7!jqd!h8!jb!jl9!jkf!nic!p7!nj1!jj5!nj8!jvb!kg7!nkd!iu2!nlc\2st$9@3$6@2$2$3$3@1$c^1@4$8@2$2$0$1@2$2$3$3\2kr@2$2$0$1@1$a@3$7$0$1^1@5$d$0$1@4$e$0$5$4$1@4$f$0$5$4$1@1$b^1").
Definition bad_answer {R} (bail : M R) : M R := SVis (EUndef UBadAnswer) (fun _ => bail).

(* [comment removed for export] *)
Definition brk_pages_ok : ltac2:(zQ "30!jb!oc!jj5>2st$2>2lo$0>3len$0$1") := ltac2:(zQ "90!pc!jb!ikf!nm9!jj5!imf!hg3!iga!hlc\2st$4\2lo$1\3len$1@2$0@2$0@2$8Z^2@2$7@2$6^2^1$2@3$5@1$3^3^2^1").

(* [comment removed for export] *)
Definition new_region : ltac2:(zQ "50!jb!jj5!h8!j7!nhb>1k$4>4base$0>3len$0>2st$1@2$2$1$3") := ltac2:(zQ "h20!j7!jqd!jl9!jkf!jb!jj5!iu2!vd!nn7!nhb!jue!jvb!no2!np1!npf!lr4!ltc!ln8\1k$9\4base$4\3len$4\2st$5=3rid$0@1$a^1@4$7$5$0@2$c@1$e^1@2$d@7$f$0$1@4$6$0$3$2$1@4$h0$0$1@4$6$0$3$2$1@4$h1$0$3$2$1^1@3$8^5^4^3@1$b^2^2^1").
(* [comment removed for export] *)
Definition drop_region : ltac2:(zQ "20!jj5!j7>3rid$1>2st$0$0") := ltac2:(zQ "e0!j7!jl9!jkf!jqd!ind!iu2!lqa!lse!ln8!jj5!jvb!khf!np1!nq6\3rid$0\2st$9@2$d@5$6$0@4$5$0$2$1$4@4$7$0$4@4$5$0$2$1$4@4$8$0$2$1$4^2@1$b^1@2$c@5$6$0@4$5$0$2$1$3@4$7$0$3@4$5$0$2$1$3@4$8$0$2$1$3^2@1$a^1^1").
Definition del_group : ltac2:(zQ "20!jj5!o5>1g$1>2st$0$0") := ltac2:(zQ "h11!j7!jb!o5!jkf!ir7!jq6!jl9!ip7!jm8!job!iu2!jj5!jt9!mu0!lqa!lse!ln8&@4$a$2@4$9$0$3$1$4@6$8$0$3$6$1$4$7$5\1g$2\2st$b@2$d@5$e$2~0@4$f$2$5~0@4$h0$2@4$9$0$3$1$4@6$8$0$3$6$1$4$7$5^2@1$c^1^1").

(* [comment removed for export] *)
Definition add_slots : ltac2:(zQ "30!jb!o5!jj5>1m$1>1p$1>6stride$0>3cnt$0>2st$2$2") := ltac2:(zQ "h82!jb!o5!j7!jkf!ir7!h8!jl9!ip7!jm8!job!iu2!vd!hg3!p7!nr3!nra!jj5!kia!ns1!nsd!nt4!lr4!ltc!ln8&@4$a$1@4$9$2$3$0$4@6$8$2$3$6$0$4$7@2$5$1$0&@2$5$0~0\1m$1\1p$1\6stride$0\3cnt$0\2st$h0@2$h2@3$d$0~0@4$h3^2~1\3acc~1M5\3acc~1~1^1\1i$0\2tb~0@4$b$0~0@2$c^2+1@7$h5$1@2$5$1$0~0@4$h6$1@2$5$1$0~0@4$h7$1@4$9$2$3$0$4@6$8$2$3$6$0$4$7@2$5$1$0@2$f^7@2$c$e@2$h4^6^2@4$b$1$0^8^2^1@4$b$0~0Z@1$h1^1^1").
Definition del_slots : ltac2:(zQ "30!jb!jj5!o5>1p$2>6stride$0>3cnt$0>2st$1$1") := ltac2:(zQ "h82!jb!o5!j7!jkf!ir7!h8!jl9!ip7!jm8!job!iu2!vd!hg3!p7!nr3!nra!jj5!kia!ns1!nsd!nt4!lqa!lse!ln8&@4$a$1@4$9$2$3$0$4@6$8$2$3$6$0$4$7@2$5$1$0&@2$5$0~0\1p$1\6stride$0\3cnt$0\2st$h0@2$h2@3$d$0~0@4$h3^2~1\3acc~1M5\3acc~1~1^1\1i$0\2tb~0@4$b$0~0@2$c^2+1@5$h5$1~0@4$h6$1@2$5$1$0~0@4$h7$1@4$9$2$3$0$4@6$8$2$3$6$0$4$7@2$5$1$0@2$f^7@2$c$e@2$h4^6^2^1@4$b$0~0Z@1$h1^1^1").

(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive cellval := Known (v : Z) | Unknown (hint : Z).

(* [comment removed for export] *)
Definition stale : ltac2:(zQ "60!j7!jb!oc!hm8!jf!h8>2hl@1$3@2$5$1$0>1b$1>1t@1$4$0$2") := ltac2:(zQ "d0!j7!jb!jf!h8!pc!oc!p2!hm8!p7!uc!nta!nu5!hlc\2hl@1$7@2$3$1$0\1b$1\1t@1$2$0@3$a@2$3$1$0\2ch@2$3$1$0@2$4@2$c^3@3$6$1$0^1M2\1t@1$2$0$5^2\1t$0@2$b^1@3$8$1$0^2$9^3").

Definition stale_pg : ltac2:(zQ "30!jf!j7!oc>2hp@1$0$1>1t@1$0$1$2") := ltac2:(zQ "60!jf!j7!oc!u5!uc!nu5\2hp@1$0$1\1t@1$0$1M0\2hp@1$0$1$2^2\1h$1M0\1t@1$0$1$2^2\1t$1@2$5^1^2$4$3").

Definition cell_read : ltac2:(zQ "30!jb!nub!ind>1r$2>3off$0$1") := ltac2:(zQ "hc0!jb!j7!h8!hm8!ip7!ir7!oc!nub!jf!llf!iu2!lm9!jga!nv5!ih0!nvb!og3!ogd!oh5!oi0!hsd!lua!hn4!oi6!oj0!oj8!ind!lvc\1r$ha\3off$0=2hl@1$3@2$2$0$1@5$hb@1$3@2$2$0$1@1$3@2$2$0$1@1$h5@1$3@2$2$0$1@1$h6@2$2$0$1@6$9$0@1$3@2$2$0$1@4$a$0$5$4@1$3@2$2$0$1@4$b$0$5$4@1$3@2$2$0$1@2$h3^1+h0@1$h8^2=2hp@1$8$1@6$9$0$1@4$a$0$5$4$1@4$b$0$5$4$1@2$h3^2+hgg0@1$h9^3M8\1x@1$8@2$2$0$1$7@6$9$0@2$2$0$1@4$a$0$5$4@2$2$0$1@4$b$0$5$4@2$2$0$1^3@1$h7^4\1y@2$2$0$1M2\1y@2$2$0$1$7^1\1v$0\1t$1M6\0$6$7@2$e@2$h2^4@2$d$1^1@3$h1^5@2$h4^6+h0@2$d$1^1@1$h0^2@1$f^2M6\0$6$7@2$e@2$h2^1@1$c$1@3$h1^2@2$h4^3+h0@1$c$1@1$h0Z@1$fZ").

(* [comment removed for export] *)
Definition get_shadow : ltac2:(zQ "30!j7!jj5!ind>2st$1>3rid$0$2") := ltac2:(zQ "c0!ind!j7!jl9!jkf!lua!jj5!khf!ok1!llf!iu2!lm9!lvc\2st$5\3rid$1@5$b$0$0@1$4$0$7@6$8$1$0@4$9$1$3$2$0@4$a$1$3$2$0^1@1$6^2").
Definition rd8 {R} (st : mstate) (p : aptr) (k : Z -> M R) : M R :=
  match cell_read (get_shadow st (fst p)) (snd p) with
  | Known v => k v
  | Unknown hint => SVis (EPeek p (conc st p) hint) (fun v => if peek_answer_ok v then k v else bad_answer (k hint))
  end.
(* [comment removed for export] *)
Definition rd16 {R} (st : mstate) (p : aptr) (k : Z -> M R) : M R :=
  rd8 st p (fun b0 => rd8 st (aadd p 1) (fun b1 => k (b0 + 256 * b1))).
Definition rd32 {R} (st : mstate) (p : aptr) (k : Z -> M R) : M R :=
  rd8 st p (fun b0 => rd8 st (aadd p 1) (fun b1 =>
  rd8 st (aadd p 2) (fun b2 => rd8 st (aadd p 3) (fun b3 =>
  k (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3))))).

Definition upd_region : ltac2:(zQ "30!jj5!jqd!j7>3rid$2>1f>0$1$1>2st$0$0") := ltac2:(zQ "d0!jqd!j7!jl9!jkf!jf!jj5!iu2!mv6!jvb!np1!lr4!ltc!ln8\3rid$1\1f>0$0$0\2st$5M4\1x@1$4$0$5@2$7^1^3\1r$0@2$9@7$a$1$0@4$6$1$3$2$0@4$b$1$0@4$6$1$3$2$0@4$c$1$3$2$0^4@1^3^1@1$8^2^2^1").
Definition upd_shadow : ltac2:(zQ "30!jj5!ind!j7>3rid$2>1f>0$1$1>2st$0$0") := ltac2:(zQ "c0!ind!j7!jl9!jkf!iu2!okb!jj5!khf!nq6!lr4!ltc!ln8\3rid$1\1f>0$0$0\2st$6@2$8@7$9$1$0@4$4$1$3$2$0@4$a$1$0@4$4$1$3$2$0@4$b$1$3$2$0^3@1^2@2$5^1^3@1$7^1^1").
(* [comment removed for export] *)
Definition wr8 : ltac2:(zQ "30!jj5!jb!o5>1p$2>1v$1>2st$0$0") := ltac2:(zQ "h60!jb!j7!h8!ip7!ir7!iu2!p2!vd!p7!o5!iv8!jj5!oi6!oj0!oj8!kj4!ind!ol8!htc!lr4!ltc!ln8\1p$9\1v$0\2st$b@3$h1@3$6$1$0^3\1r$h0@3$a@7$h3$0@2$2$0$1@4$5$0$4$3@2$2$0$1@4$h4$0@2$2$0$1@4$5$0$4$3@2$2$0$1@4$h5$0$4$3@2$2$0$1@3$8$1$0^4@4$7$0$1@2$h2^3+vf@1$f^2@1$c^1@1$d^1@1$e^1^1").
Definition wr16 : ltac2:(zQ "30!jj5!jb!o5>1p$2>1v$1>2st$0$0") := ltac2:(zQ "60!om5!jb!nra!o5!jj5!omb\1p$3\1v$1\2st$4@3$0@2$2^3+1@2$5^2+8@3$0^3^2^1").
Definition wr32 : ltac2:(zQ "30!jj5!jb!o5>1p$2>1v$1>2st$0$0") := ltac2:(zQ "60!om5!nra!omb!jb!o5!jj5\1p$4\1v$3\2st$5@3$0@2$1^3+3@2$2^2+h8@3$0@2$1^3+2@2$2^2+h0@3$0@2$1^3+1@2$2^2+8@3$0^3^2^1").

(* [comment removed for export] *)
Definition hav_add : ltac2:(zQ "40!j7!jb!hm8!h8>3cov$1>1t$0>2hl@1$2@2$3$1$0@1$2@2$3$1$0") := ltac2:(zQ "c0!j7!jb!h8!p2!hm8!hlc!hme!vd!oo6!op1!opb!os2\3cov$1\1t$0\2hl@1$4@2$2$1$0@3$6@2$2$1$0@4$7$1$0^3^2@6$9@2$2$1$0@1$4@2$2$1$0@1$b@2$2$1$0\2ch@2$2$1$0@1$8@2$5^4@3$3$1$0^1\1x@2$2$1$0@1$a@2$5^4@3$3$1$0^1^1").

(* [comment removed for export] *)
Definition havoc_units : ltac2:(zQ "70!jb!j7!hm8!h8!ip7!iu2!ir7>1x$0>1y$0>1t$1>1h@4$5$0$6$4@1$2@2$3$0$1@4$5$0$6$4@1$2@2$3$0$1") := ltac2:(zQ "h91!jb!h8!j7!hm8!ip7!ir7!iu2!oc!vd!hg3!oi0!t8!hm2!lua!hn4!p7!ot1!nsd!hsd!lr4!llf!ltc!lm9!ln8!lvc&@2$1$0@4$6$0$5$4@1$3@2$1$0$2\1x$0\1y$0\1t$2\1h@4$6$0$5$4@1$3@2$1$0$2=2u0$0@2$a^4+h0=2u1$0@2$a@2$c^4+1+h0=7lastcov$0=1r$0@2$h2^5+h0M7\0$7$0@2$b^1Z+h0^1@3$f$0@4$6$0$5$4@1$3@2$1$0$2@4$h1@2$9@2$c^2^3+1~0\3acc~0M1\3acc~0~0^1\1u$0\1h@4$6$0$5$4@1$3@2$1$0$2=3cov$0M7\0$7$0@2$b^2^5^4+h0@4$8$0@4$6$0$5$4@1$3@2$1$0$2@2$9^3+1@7$h3$0@1$3@2$1$0$2@4$6$0$5$4@1$3@2$1$0$2@4$h5$0@1$3@2$1$0$2@4$6$0$5$4@1$3@2$1$0$2@4$h7$0$5$4@1$3@2$1$0$2^3@3$h0^1^9@5$h8@1$3@2$1$0$2@1$3@2$1$0$2@1$d@1$3@2$1$0$2@1$e@2$1$0$2@6$h4$0@1$3@2$1$0$2@4$6$0$5$4@1$3@2$1$0$2@4$h6$0$5$4@1$3@2$1$0$2^3^2^2@4$8$0@4$6$0$5$4@1$3@2$1$0$2^3^4").

Definition havoc_pages : ltac2:(zQ "50!jb!j7!ip7!iu2!ir7>2p0$0>2p1$0>1t$1>1h@4$3$0$4$2$1@4$3$0$4$2$1") := ltac2:(zQ "e0!jb!j7!ip7!ir7!iu2!h8!vd!p7!hg3!nsd!hm2!lr4!ltc!ln8\2p0$0\2p1$0\1t$1\1h@4$4$0$3$2$1@3$7$0@4$4$0$3$2$1@4$9@2$a^3^4@2$5$0@4$4$0$3$2$1\3acc@2$5$0@4$4$0$3$2$1M5\3acc@2$5$0@4$4$0$3$2$1@2$5$0@4$4$0$3$2$1^1\2pg$0\1h@4$4$0$3$2$1@4$6$0@4$4$0$3$2$1@2$8^2+1@7$b$0$1@4$4$0$3$2$1@4$c$0$1@4$4$0$3$2$1@4$d$0$3$2$1^2^5^1@4$6$0@4$4$0$3$2$1^4^1").

Definition havoc (p : aptr) (n : Z) (st : mstate) : mstate :=
  if n <=? 0 then st else
  let a := snd p in
  let b := a + n in
  let t := s_tick st in
  let fp := (a + 4095) / 4096 in      (* [comment removed for export] *)
  let lp := b / 4096 in               (* [comment removed for export] *)
  upd_shadow (fst p) (fun r =>
    let '(hav, havp) :=
      if fp <? lp then
        (* [comment removed for export] *)
        let hav1 := if a <? fp * 4096 then havoc_units a (fp * 4096) t (r_hav r) else r_hav r in
        let hav2 := if lp * 4096 <? b then havoc_units (lp * 4096) b t hav1 else hav1 in
        (hav2, havoc_pages fp lp t (r_havp r))
      else (havoc_units a b t (r_hav r), r_havp r) in
    mkShadow (r_cells r) hav havp) st.

(* [comment removed for export] *)
Definition guard {R} (tag : Z) (c : bool) (k : M R) (bail : M R) : M R :=
  if c then k else SVis (EUndef (UAssert tag)) (fun _ => bail).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition step_seq : ltac2:(zQ "10!jj5>2st$0$0") := ltac2:(zQ "h00!jb!oc!li3!jh9!jj5!otb!lq0!ip7!ir7!ll9!ou5!hg3!t8!isd!iu2!iua\2st$4M1\0$1$4@2$c@1$2@1$9^1+vf@2$6\1c$3@2$5+1@2$a@2$d@4$e$0$8$7$0@4$f$0$8$7$0^1^1@2$6\1c$3@2$5@2$b@1$2^1+1^1^1").

Definition sc_in_seq_range : ltac2:(zQ "20!oc!jb>2sc$1$0") := ltac2:(zQ "40!pc!jb!iga!hlc\2sc$1@2$0@2$2+7^1@2$3^1+i7").  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition record_seq : ltac2:(zQ "20!jj5!jb>2sc$1>2st$0$0") := ltac2:(zQ "h00!jb!ip7!ir7!oc!jj5!iu2!li3!lib!jh9!ova!ou5!lq0!hm2!lr4!ltc!ln8\2sc$0\2st$4M3\0$3$4@1$9^2@2$b\1c$8@2$a@7$d$0$0@4$5$0$2$1$0@4$e$0$0@4$5$0$2$1$0@4$f$0$2$1$0@2$c^3+7@1$6^1@1$7^1^1^1^1").

(* [comment removed for export] *)
Definition account_bounce : ltac2:(zQ "20!jj5!jb>2sc$1>2st$0$0") := ltac2:(zQ "f0!oc!hm2!jj5!jb!pgc!ph6!hg3!hlc!pc!pi3!li3!ll9!ova!pi9!t8\2sc$3\2st$2M0\0$0$2@1$c^2=3seq$3@2$d^1@2$1^2+7M0\0$0$2@2$8@1$9@2$e^1Z@2$7@2$1@1$a@1$b^2^1+aM0\0$0$2@2$7@2$6@2$4^2@2$1^3+7+1+m4@3$5@2$1^3+7@2$6@2$4^2@2$1^3+7+1^2@3$5@2$1^3+7+p6^2^2^1").

(* [comment removed for export] *)
Definition decay_bounces : ltac2:(zQ "20!jj5!jb>2sc$1>2st$0$0") := ltac2:(zQ "a0!hm2!oc!pgc!jj5!pc!pi3!jb!ova!ph6!t8\2sc$6\2st$3M1\0$1$3@2$4@1$7^2@1$5@2$9@2$2^1@2$0^2+7Z@3$8@2$0^2+7@2$0@2$2^1@2$0^2+7+1^1^1").

(* [comment removed for export] *)
Definition is_bouncing : ltac2:(zQ "30!oc!jb!jj5>2sc$1>2st$2$0") := ltac2:(zQ "70!pc!jb!pgc!jj5!ova!iga!hm2\2sc$1\2st$3@2$0@1$4^2@2$5+m4@2$2^1@2$6^2+7").

(* [comment removed for export] *)
Definition size_to_class : ltac2:(zQ "10!jb>1n$0$0") := ltac2:(zQ "a0!jb!oc!hg3!hlc!pj5!hm2!pk2!pk7!nt4!omb\1n$0=1n$0@2$9@2$5@2$2^1$6+1+4M1\0$1$0@2$3^1+a^1=1n$0@2$2^1+1=1i$0@2$2@2$8@2$5+hc@1$7^1+4+8=1i$0M1\0$1$0@2$3@1$4@2$2^1+1^2@2$2^1+2^1M1\0$1$0@2$3@1$4^1^3@2$2^1+1^1").

(* [comment removed for export] *)
Definition size_overflows : ltac2:(zQ "20!oc!jb>1n$1$0") := ltac2:(zQ "40!hm2!jb!iga!ht6\1n$1@2$2@2$0@2$0@2$3+2+jf+1+hgg0^1").

(* [comment removed for export] *)
Inductive lhead := LActive (sc : Z) | LFree.
Definition get_head : ltac2:(zQ "30!pkf!jj5!te>2st$1>1h$0$2") := ltac2:(zQ "70!pkf!jb!pl7!kr2!ll9!jj5!te\2st$5\1h$0M0\1h$0$6^1\2sc$1@2$2^3^1@1$3@1$4^2").
Definition set_head : ltac2:(zQ "30!jj5!pkf!te>1h$1>1v$2>2st$0$0") := ltac2:(zQ "70!pkf!jj5!jb!te!pm0!pmd!lq0\1h$0\1v$3\2st$1M0\1h$0$1^3\2sc$2@3$4^1^3^2@2$6@1$5^2^1").

(* [comment removed for export] *)
Definition queue {R} (h : lhead) (m : aptr) (st : mstate) (k : mstate -> M R) (bail : M R) : M R :=
  let mr := get_meta_rec st m in
  guard 1 (optr_eqb (m_next mr) None) (
  guard 2 (optr_eqb (m_prev mr) None) (
  match get_head st h with
  | Some head =>
      let hprev := m_prev (get_meta_rec st head) in
      (* [comment removed for export] *)
      let st1 := upd_meta m (fun r => m_set_prev hprev (m_set_next (Some head) r)) st in
      (* [comment removed for export] *)
      let st2 := match hprev with Some pv => upd_meta pv (m_set_next (Some m)) st1 | None => st1 end in
      let st3 := upd_meta head (m_set_prev (Some m)) st2 in
      k st3
  | None =>
      let st1 := upd_meta m (fun r => m_set_prev (Some m) (m_set_next (Some m) r)) st in
      k (set_head h (Some m) st1)
  end) bail) bail.

(* [comment removed for export] *)
Definition dequeue : ltac2:(zQ "30!jj5!o5!pkf>1h$2>1m$1>2st$0$0") := ltac2:(zQ "h20!o5!jj5!oc!jf!mpc!jga!po3!nv5!mr3!poe!ppb!jg3!pq8!pr3!pi3!pre!mk1!pkf\1h$h1\1m$0\2st$1=2mr$b@2$h0^1^2=3st1$1M2\0$2$1@1$e@2$c@1$4^1@2$7$0^3=3st1$1M3\1x@1$3$0$1@1$8^1\2pv$0@3$6^1@1$9@1$4^2^3^2=3st2$1M3\1x@1$3$0$1@1$4^2\2nx$0@3$6^1@1$a@1$8^3^2^1M2\0$2$1@2$c@2$f^1^6@2$7$0^5@3$d^6@1$4^3^1^1@3$d^4@1$5$0^2@3$6^4\1r$b@2$a@1$5$0@2$9@1$5$0^1^1").

(* [comment removed for export] *)
Definition free_meta {R} (m : aptr) (st : mstate) (k : mstate -> M R) (bail : M R) : M R :=
  queue LFree m (put_meta m meta0 st) k bail.

(* [comment removed for export] *)
Definition activate_group {R} (m : aptr) (st : mstate) (k : mstate -> Z -> M R) (bail : M R) : M R :=
  let mr := get_meta_rec st m in
  guard 3 (m_avail mr =? 0) (
    let act := match m_mem mr with Some _ => mask_upto (group_active_idx st (default (0%N,-1) (m_mem mr))) | None => 0 end in
    let mask := m_freed mr in
    let st1 := upd_meta m (fun r => m_set_avail (Z.land mask act) (m_set_freed (Z.ldiff mask act) r)) st in
    k st1 (Z.land mask act)) bail.

(* [comment removed for export] *)
Definition get_stride : ltac2:(zQ "20!jb!jg3>2mr$1$0") := ltac2:(zQ "d0!oc!nr3!mo9!t8!nt4!pc!pi3!jb!mnc!mq5!jg3!pj5!hm2\2mr$aM0\0$0$7@2$5@2$3@1$8^1Z@1$6@2$3@1$2^1Z@2$c@2$4@1$2^1+hgg0$1@2$4$1@1$b@1$9^1").

(* [comment removed for export] *)
Definition area_of : ltac2:(zQ "10!o5>1m$0$0") := ltac2:(zQ "80!j7!jb!p7!p2!vd!o5!hsd!hm2\1m$5@4$4$0$1@3$3$0$1^1@2$7@3$2$0$1^1@2$6@3$2$0$1^1+hgg0").

(* [comment removed for export] *)
Definition get_meta {R} (st : mstate) (p : aptr) (k : aptr -> Z -> Z -> M R) (bail : M R) : M R :=
  guard 10 (snd p mod 16 =? 0) (
  rd16 st (aadd p (-2)) (fun offset16 =>
  rd8 st (aadd p (-3)) (fun b3 =>
  let index := Z.land b3 31 in
  rd8 st (aadd p (-4)) (fun b4 =>
  let cont (offset : Z) :=
    let base := aadd p (- (UNIT * offset) - UNIT) in
    match get_group st base with
    | None => SVis (EUndef UBadPtr) (fun _ => bail)
    | Some gh =>
      match g_meta gh with
      | None => SVis (EUndef UBadPtr) (fun _ => bail)
      | Some m =>
        let mr := get_meta_rec st m in
        guard 11 (optr_eqb (m_mem mr) (Some base)) (
        guard 12 (index <=? m_last_idx mr) (
        guard 13 (negb (testbit (m_avail mr) index)) (
        guard 14 (negb (testbit (m_freed mr) index)) (
        let ar := (s_areas st) !! (area_of m) in
        guard 15 (match ar with Some a => a_check a =? c_secret (ctx st) | None => false end) (
        let sc := m_sizeclass mr in
        guard 16 (if sc <? 48 then (size_class sc * index <=? offset) && (offset <? size_class sc * (index + 1))
                  else sc =? 63) (
        guard 17 (if negb (m_maplen mr =? 0) then offset <=? m_maplen mr * 4096 / UNIT - 1 else true) (
        k m offset index) bail) bail) bail) bail) bail) bail) bail
      end
    end in
  if negb (b4 =? 0) then
    guard 18 (offset16 =? 0) (
    rd32 st (aadd p (-8)) (fun offset32 =>
    guard 19 (65535 <? offset32) (cont offset32) bail)) bail
  else cont offset16)))) bail.

(* [comment removed for export] *)
Definition get_nominal_size {R} (st : mstate) (p e : aptr) (k : Z -> M R) (bail : M R) : M R :=
  rd8 st (aadd p (-3)) (fun b3 =>
  let reserved := Z.shiftr b3 5 in
  let cont (reserved : Z) :=
    guard 22 (reserved <=? snd e - snd p) (
    rd8 st (aadd e (- reserved)) (fun cb =>
    guard 23 (cb =? 0) (
    rd8 st e (fun eb =>
    guard 24 (eb =? 0) (k (snd e - reserved - snd p)) bail)) bail)) bail in
  if 5 <=? reserved then
    guard 20 (reserved =? 5) (
    rd32 st (aadd e (-4)) (fun r32 =>
    guard 21 (5 <=? r32) (
    rd8 st (aadd e (-5)) (fun b5 =>
    guard 25 (b5 =? 0) (cont r32) bail)) bail)) bail
  else cont reserved).

(* [comment removed for export] *)
Definition set_size (p e : aptr) (n : Z) (b3 : Z) (st : mstate) : mstate :=
  let reserved := snd e - snd p - n in
  let st1 := if negb (reserved =? 0) then wr8 (aadd e (- reserved)) 0 st else st in
  let '(st2, reserved) :=
    if 5 <=? reserved then (wr8 (aadd e (-5)) 0 (wr32 (aadd e (-4)) reserved st1), 5)
    else (st1, reserved) in
  wr8 (aadd p (-3)) (Z.land b3 31 + Z.shiftl reserved 5) st2.

(* [comment removed for export] *)
Fixpoint zero_hdrs (p : aptr) (size : Z) (i : Z) (cnt : nat) (st : mstate) : mstate :=
  match cnt with
  | O => st
  | S c => zero_hdrs p size (i + 1) c (wr8 (aadd p (UNIT + i * size - 4)) 0 st)
  end.

(* [comment removed for export] *)
Definition fold_off : ltac2:(zQ "10!jb>3off$0>5slack$0$0") := ltac2:(zQ "80!jb!oc!ps9!omb!hlc!hg3!htc!hm2\3off$0\5slack$0M1\0$1$0@2$4^1^2=1m$0^1=1m$0@2$2^1@2$3^1+1=1m$0@2$2^1@2$3^1+2=1m$0@2$2^1@2$3^1+4=3off$0@2$6^6^1M1\0$1$0@2$4^6^1@2$7^1@2$5^6+1^1^2").

Definition slot_start : ltac2:(zQ "30!jb!jg3!te>2mr$1>3idx$0$2") := ltac2:(zQ "d0!o5!jf!jga!nv5!jb!nr3!nra!psf!mp4!jg3!te!hg3!nt4\2mr$9\3idx$4M1\1x@1$1$0$a@1$8^2\1g$0@2$3$0@2$6^1@2$b$5@2$c@1$7^3^2@1$2$0").
(* [comment removed for export] *)
Definition slot_start' : ltac2:(zQ "30!jb!o5!jg3>2mr$2>3idx$0$1") := ltac2:(zQ "e0!jb!j7!h8!lua!vd!jpa!nr3!nra!psf!mp4!jg3!hg3!nt4!lvc\2mr$a\3idx$0@2$7@5$d@2$2$1$0@2$2$1$0@1$3@2$2$1$0@4$4$1$0$5Z@1$9^2@2$b$6@2$c@1$8^2^1").
Definition slot_of : ltac2:(zQ "30!o5!jb!jj5>2st$2>1g$0>3idx$1$0") := ltac2:(zQ "50!jb!o5!mk1!jj5!ptc\2st$3\1g$1\3idx$0@2$4@2$2^3^2^1").

(* [comment removed for export] *)
Definition enframe_read_off {R} (st : mstate) (g : aptr) (idx n ctr : Z) (k : Z -> M R) : M R :=
  let mr := get_meta_rec st g in
  let stride := get_stride mr in
  let slack := (stride - IB - n) / UNIT in
  let p := slot_start' mr idx in
  rd8 st (aadd p (-3)) (fun b3 =>
    if negb (b3 =? 0) then rd16 st (aadd p (-2)) (fun o16 => k (fold_off (Z.land (o16 + 1) 255) slack))
    else k (fold_off (Z.land ctr 255) slack)).

(* [comment removed for export] *)
Definition enframe_at (st : mstate) (g : aptr) (idx n off : Z) : mstate * aptr :=
  let mr := get_meta_rec st g in
  let stride := get_stride mr in
  let gm := default (0%N, 0) (m_mem mr) in
  let p := aadd gm (UNIT + stride * idx) in
  let e := aadd p (stride - IB) in
  let '(st1, p) :=
    if negb (off =? 0) then
      let st1 := wr16 (aadd p (-2)) off st in
      let st2 := wr8 (aadd p (-3)) 224 st1 in
      let p' := aadd p (UNIT * off) in
      (wr8 (aadd p' (-4)) 0 st2, p')
    else (st, p) in
  let st2 := wr16 (aadd p (-2)) ((snd p - (snd gm + UNIT)) / UNIT) st1 in
  let st3 := wr8 (aadd p (-3)) idx st2 in
  (set_size p e n idx st3, p).

Definition enframe_full {R} (st : mstate) (g : aptr) (idx n ctr : Z) (k : mstate -> aptr -> M R) : M R :=
  enframe_read_off st g idx n ctr (fun off => let '(st1, p) := enframe_at st g idx n off in k st1 p).

(* [comment removed for export] *)
Definition nest_layout (st : mstate) (g : aptr) (idx j : Z) (size cnt : Z) : mstate :=
  let '(st1, p) := enframe_at st g idx (UNIT * size_class j - IB) 0 in
  let st2 := wr8 (aadd p (-3)) (Z.lor (Z.land idx 31) 192) st1 in
  zero_hdrs p size 0 (Z.to_nat (cnt + 1)) st2.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition am_take {R} (st : mstate) (k : mstate -> optr -> M R) (bail : M R) : M R :=
  match c_avail_meta (ctx st) with
  | None => SVis (EUndef UBadPtr) (fun _ => bail)
  | Some m =>
    let st1 := upd_ctx (fun c => set_avail_meta (Some (aadd m META_SIZE)) (set_avail_meta_count (c_avail_meta_count c - 1) c)) st in
    let st2 := upd_meta m (fun r => m_set_prev None (m_set_next None r)) st1 in
    k st2 (Some m)
  end.

(* [comment removed for export] *)
Definition am_carve {R} (st : mstate) (p : aptr) (k : mstate -> optr -> M R) (bail : M R) : M R :=
  let st1 := upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096))
                                (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st in
  let st2 := match c_meta_area_tail (ctx st1) with
             | Some tl => set_areas (<[tl := match (s_areas st1) !! tl with
                                              | Some a => mkArea (a_check a) (Some p) (a_nslots a)
                                              | None => mkArea 0 (Some p) 0 end]> (s_areas st1)) st1
             | None => upd_ctx (set_meta_area_head (Some p)) st1
             end in
  let st3 := upd_ctx (set_meta_area_tail (Some p)) st2 in
  let old := default (mkArea 0 None 0) ((s_areas st3) !! p) in
  let st4 := set_areas (<[p := mkArea (c_secret (ctx st3)) (a_next old) NSLOTS]> (s_areas st3)) st3 in
  let st5 := upd_ctx (fun c => set_avail_meta (Some (aadd p AREA_HDR)) (set_avail_meta_count NSLOTS c)) st4 in
  am_take st5 k bail.

(* [comment removed for export] *)
Definition am_finish {R} (st : mstate) (need_unprotect : bool) (k : mstate -> optr -> M R) (bail : M R) : M R :=
  match c_avail_meta_areas (ctx st) with
  | None => SVis (EUndef UBadPtr) (fun _ => bail)
  | Some p =>
    let need_unprotect := if negb (snd p mod PGSZ =? 0) then false else need_unprotect in
    if need_unprotect then
      SVis (EMprotect (conc st p) PGSZ PROT_RW) (fun r =>
        if negb (mprotect_answer_ok r) then bad_answer bail else
        if (r =? 0) || (r =? TWO64 - ENOSYS) then am_carve st p k bail else k st None)
    else am_carve st p k bail
  end.

(* [comment removed for export] *)
Definition am_after_brk {R} (st : mstate) (need_unprotect : bool) (k : mstate -> optr -> M R) (bail : M R) : M R :=
  if c_avail_meta_area_count (ctx st) =? 0 then
    let n := Z.shiftl 2 (c_meta_alloc_shift (ctx st)) in
    SVis (EMmap 0 (n * PGSZ) PROT_NONE (MAP_PRIVATE + MAP_ANON)) (fun r =>
      if negb (mmap_answer_ok (live_ranges st) (n * PGSZ) r) then bad_answer bail else
      if is_err r then k st None else
      let '(st1, rid) := new_region RKMeta r (n * PGSZ) st in
      let st2 := upd_ctx (fun c => set_meta_alloc_shift (c_meta_alloc_shift c + 1)
                                    (set_avail_meta_area_count (n - 1)
                                    (set_avail_meta_areas (Some (rid, PGSZ)) c))) st1 in
      am_finish st2 need_unprotect k bail)
  else am_finish st need_unprotect k bail.

(* [comment removed for export] *)
Definition alloc_meta {R} (st : mstate) (k : mstate -> optr -> M R) (bail : M R) : M R :=
  (* [comment removed for export] *)
  let st := if c_init_done (ctx st) =? 0
            then upd_ctx (fun c => set_init_done 1 (set_secret (s_secret st) c)) st
            else st in
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  match c_free_meta_head (ctx st) with
  | Some m => k (dequeue LFree m st) (Some m)
  | None =>
    (* [comment removed for export] *)
    if negb (c_avail_meta_count (ctx st) =? 0) then am_take st k bail else
    (* [comment removed for export] *)
    let brk_dead := match c_brk (ctx st) with BrkDead => true | _ => false end in
    if (c_avail_meta_area_count (ctx st) =? 0) && negb brk_dead then
      match c_brk (ctx st) with
      | BrkUntried =>
        (* [comment removed for export] *)
        SVis (EBrk 0) (fun cur =>
          if negb (brk0_answer_ok cur) then bad_answer bail else
          let base := round_up_pg cur in
          let new := base + 2 * PGSZ in
          SVis (EBrk new) (fun r =>
            if negb (brk_answer_ok cur new r) then bad_answer bail else
            if negb (r =? new) then am_after_brk (upd_ctx (set_brk BrkDead) st) true k bail
            else if negb (brk_pages_ok st base (2 * PGSZ)) then bad_answer bail   (* [comment removed for export] *)
            else
              (* [comment removed for export] *)
              SVis (EMmap base PGSZ PROT_NONE (MAP_PRIVATE + MAP_ANON + MAP_FIXED)) (fun rg =>
                if negb (mmap_fixed_answer_ok base rg) then bad_answer bail else
                (* [comment removed for export] *)
                let '(st1, rid) := new_region RKBrk base (2 * PGSZ) st in
                let st2 := upd_ctx (fun c => set_avail_meta_area_count 1
                                              (set_avail_meta_areas (Some (rid, PGSZ))
                                              (set_brk (BrkLive rid (2 * PGSZ)) c))) st1 in
                am_after_brk st2 false k bail)))
      | BrkLive rid off =>
        (* [comment removed for export] *)
        let old := conc st (rid, off) in
        let new := old + PGSZ in
        SVis (EBrk new) (fun r =>
          if negb (brk_answer_ok old new r) then bad_answer bail else
          if negb (r =? new) then am_after_brk (upd_ctx (set_brk BrkDead) st) true k bail
          else if negb (brk_pages_ok st old PGSZ) then bad_answer bail   (* [comment removed for export] *)
          else
            let st1 := upd_region rid (fun rg => mkRegion (r_kind rg) (r_base rg) (off + PGSZ)) st in
            let st2 := upd_ctx (fun c => set_avail_meta_area_count 1
                                          (set_avail_meta_areas (Some (rid, off))
                                          (set_brk (BrkLive rid (off + PGSZ)) c))) st1 in
            am_after_brk st2 false k bail)
      | BrkDead => am_after_brk st true k bail (* [comment removed for export] *)
      end
    else am_after_brk st true k bail
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint span_loop (fuel : nat) (cnt span size : Z) : Z :=
  match fuel with
  | O => cnt
  | S f => if Z.lxor span (span + size - 1) <? 4096 then span_loop f (cnt + 1) (span + size) size else cnt
  end.

(* [comment removed for export] *)
Definition ta_fin {R} (st : mstate) (m : aptr) (mask : Z) (k : mstate -> Z -> M R) : M R :=
  let first := lowbit mask in
  k (upd_meta m (m_set_avail (mask - first)) st) first.

Definition try_avail {R} (sc : Z) (st : mstate) (k : mstate -> Z -> M R) (bail : M R) : M R :=
  match active st sc with
  | None => k st 0
  | Some m =>
    let mask := m_avail (get_meta_rec st m) in
    let fin (st : mstate) (m : aptr) (mask : Z) : M R := ta_fin st m mask k in
    if negb (mask =? 0) then fin st m mask else
    (* [comment removed for export] *)
    let step1 : option (mstate * aptr) :=
      if m_freed (get_meta_rec st m) =? 0 then
        let st1 := dequeue (LActive sc) m st in
        match active st1 sc with None => None | Some m1 => Some (st1, m1) end
      else
        match m_next (get_meta_rec st m) with
        | Some m1 => Some (set_active sc (Some m1) st, m1)
        | None => None (* [comment removed for export] *)
        end in
    match step1 with
    | None => if m_freed (get_meta_rec st m) =? 0 then k (dequeue (LActive sc) m st) 0
              else SVis (EUndef UBadPtr) (fun _ => bail)
    | Some (st1, m1) =>
      let mask := m_freed (get_meta_rec st1 m1) in
      (* [comment removed for export] *)
      let '(st2, m2, mask) :=
        let mr := get_meta_rec st1 m1 in
        if (mask =? mask_upto (m_last_idx mr)) && negb (m_freeable mr =? 0) then
          match m_next mr with
          | Some mn => (set_active sc (Some mn) st1, mn, m_freed (get_meta_rec st1 mn))
          | None => (st1, m1, mask) (* [comment removed for export] *)
          end
        else (st1, m1, mask) in
      (* [comment removed for export] *)
      let mr2 := get_meta_rec st2 m2 in
      let gai := match m_mem mr2 with Some _ => group_active_idx st2 (default (0%N,-1) (m_mem mr2)) | None => 0 end in
      let '(st3, m3) :=
        if Z.land mask (mask_upto gai) =? 0 then
          if negb (optr_eqb (m_next mr2) (Some m2)) then
            match m_next mr2 with
            | Some mn => (set_active sc (Some mn) st2, mn)
            | None => (st2, m2) (* [comment removed for export] *)
            end
          else
            let cnt := gai + 2 in
            let size := size_class (m_sizeclass mr2) * UNIT in
            let span := UNIT + size * cnt in
            let cnt := span_loop 300%nat cnt span size in
            let cnt := if m_last_idx mr2 + 1 <? cnt then m_last_idx mr2 + 1 else cnt in
            match m_mem mr2 with
            | Some g => (set_group_active_idx g (cnt - 1) st2, m2)
            | None => (st2, m2)
            end
        else (st2, m2) in
      (* [comment removed for export] *)
      activate_group m3 st3 (fun st4 mask =>
        guard 40 (negb (mask =? 0)) (
          fin (decay_bounces (m_sizeclass (get_meta_rec st4 m3)) st4) m3 mask) bail) bail
    end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition small_cnt_pick : ltac2:(zQ "10!jb>2sc$0>5usage$0$0") := ltac2:(zQ "60!pua!oc!jb!pi3!hlc!nt4\2sc$2\5usage$2M1\0$1$2@1$3@2$4^1@2$5+4@2$0^2Z@2$0^2ZM1\0$1$2@1$3@2$4^1@2$5+4@2$0^2+1@2$0^2+1@2$0^2+2").

(* [comment removed for export] *)
Fixpoint halve_even (fuel : nat) (cnt usage : Z) : Z :=
  match fuel with
  | O => cnt
  | S f => if (Z.even cnt) && (usage <? 4 * cnt) then halve_even f (Z.shiftr cnt 1) usage else cnt
  end.
(* [comment removed for export] *)
Fixpoint halve_big (fuel : nat) (cnt size : Z) : Z :=
  match fuel with
  | O => cnt
  | S f => if 65536 * UNIT <=? size * cnt then halve_big f (Z.shiftr cnt 1) size else cnt
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hdr_havoc : ltac2:(zQ "20!jj5!o5>1b$1>2st$0$0") := ltac2:(zQ "hc0!jb!j7!h8!hm8!ip7!ir7!iu2!p7!oj0!oi0!p2!lua!hn4!o5!ot1!iv8!jj5!oi6!oj8!kj4!ind!ol8!lr4!llf!ltc!lm9!ln8!lvc\1b$d\2st$h0@3$h5@3$a$1$0^2\1r$h4@3$f@1$h1^1@7$h6$0@1$3@2$2$0$1@4$6$0$5$4@1$3@2$2$0$1@4$h8$0@1$3@2$2$0$1@4$6$0$5$4@1$3@2$2$0$1@4$ha$0$5$4@1$3@2$2$0$1@2$9@3$7$1$0^3+h0@3$e+c@1$h3^2@5$hb@1$3@2$2$0$1@1$3@2$2$0$1@1$b@1$3@2$2$0$1@1$c@2$2$0$1@6$h7$0@1$3@2$2$0$1@4$6$0$5$4@1$3@2$2$0$1@4$h9$0$5$4@1$3@2$2$0$1@2$9@3$7$1$0^3+h0@1$8^1@1$8^1@1$h2^1^1").

Record layout_hook : Type := mkLay {
  lh_nest : mstate -> aptr -> Z -> Z -> Z -> Z -> mstate;   (* [comment removed for export] *)
  lh_hdr : mstate -> aptr -> mstate                          (* [comment removed for export] *)
}.
Definition lay_none : ltac2:(zQ "10!pv6$0") := ltac2:(zQ "40!jb!o5!jj5!qg4@2$3\2st$2\0$1\0$0\0$0\0$0\0$0^6\2st$2\0$1^2").
Definition full_lay : ltac2:(zQ "10!pv6$0") := ltac2:(zQ "50!o5!qgc!qg4!jj5!qh8@2$2$4\2st$3\1b$0@2$1^1^2").

(* [comment removed for export] *)
Definition ag_tail {R} (lay : layout_hook) (st : mstate) (sc : Z) (m : aptr) (p : aptr) (cnt active_idx : Z) (k : mstate -> optr -> M R) : M R :=
  let st := lh_hdr lay st p in                (* [comment removed for export] *)
  let st1 := set_usage sc (usage st sc + cnt) st in
  let avail := mask_upto active_idx in
  let freed := mask_upto (cnt - 1) - avail in
  let st2 := upd_meta m (fun r =>
               m_set_sizeclass sc (m_set_freeable 1 (m_set_last_idx (cnt - 1)
               (m_set_mem (Some p) (m_set_freed freed (m_set_avail avail r)))))) st1 in
  let st3 := put_group p (Some m) active_idx st2 in
  (* [comment removed for export] *)
  let st4 := add_slots m p (get_stride (get_meta_rec st3 m)) cnt st3 in
  k st4 (Some m).

Section ALLOC_GROUP.
Variable R : Type.
Variable lay : ltac2:(zQ "10!pv6$0").
Variable alloc_slot_rec : ltac2:(zQ "30!jb!qk1!jj5>0$2>0$0>0$0>0>0$2>0$0@1$1?1R>0@1$1?1R@1$1?1R").

Definition alloc_group (st : mstate) (sc req : Z) (k : mstate -> optr -> M R) (bail : M R) : M R :=
  let size := UNIT * size_class sc in
  (* [comment removed for export] *)
  alloc_meta st (fun st mo =>
  match mo with
  | None => k st None
  | Some m =>
    let usage0 := usage st sc in
    let cnt :=
      if sc <? 9 then small_cnt_pick sc usage0
      else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) usage0) size in
    (* [comment removed for export] *)
    let cnt := if (cnt =? 1) && (size * cnt + UNIT <=? PGSZ / 2) then 2 else cnt in
    let tail (st : mstate) (p : aptr) (cnt active_idx : Z) : M R := ag_tail lay st sc m p cnt active_idx k in
    if PGSZ / 2 <? size * cnt + UNIT then
      (* [comment removed for export] *)
      let nosmall := is_bouncing sc st in
      let st1 := step_seq (account_bounce sc st) in
      let usage1 := if (Z.even sc) && (sc <? 32) then usage0 + usage st1 (sc + 1) else usage0 in
      let cnt :=
        if (usage1 <? 4 * cnt) && negb nosmall then
          if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt) then 2
          else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt) then 3
          else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt) then 3
          else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt) then 5
          else cnt
        else cnt in
      let needed := round_up_pg (size * cnt + UNIT) in
      let '(cnt, needed) :=
        if negb nosmall && (cnt <=? 7) then
          let req := round_up_pg (req + IB + UNIT) in
          if (req <? size + UNIT) || ((4 * PGSZ <=? req) && (usage1 <? 2 * cnt)) then (1, req) else (cnt, needed)
        else (cnt, needed) in
      SVis (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
        if negb (mmap_answer_ok (live_ranges st1) needed r) then bad_answer bail else
        if is_err r then free_meta m st1 (fun st2 => k st2 None) bail
        else
          let '(st2, rid) := new_region RKGroup r needed st1 in
          (* [comment removed for export] *)
          let st3 := upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2 in
          let st4 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st3 in
          let ai := (4096 - UNIT) / size - 1 in
          let ai := if cnt - 1 <? ai then cnt - 1 else ai in
          let ai := if ai <? 0 then 0 else ai in
          tail st4 (rid, 0) cnt ai)
    else
      (* [comment removed for export] *)
      let j := size_to_class (UNIT + cnt * size - IB) in
      alloc_slot_rec st j (UNIT + cnt * size - IB) (fun st1 idx =>
        if idx <? 0 then free_meta m st1 (fun st2 => k st2 None) bail
        else
          match active st1 j with
          | None => SVis (EUndef UBadPtr) (fun _ => bail)
          | Some g =>
            (* [comment removed for export] *)
            let p := slot_of st1 g idx in
            let st2 := lh_nest lay st1 g idx j size cnt in      (* [comment removed for export] *)
            let st3 := upd_meta m (m_set_maplen 0) st2 in
            tail st3 p cnt (cnt - 1)
          end) bail
  end) bail.
End ALLOC_GROUP.

(* [comment removed for export] *)
Fixpoint alloc_slot {R} (lay : layout_hook) (fuel : nat) (st : mstate) (sc req : Z) (k : mstate -> Z -> M R) (bail : M R) {struct fuel} : M R :=
  match fuel with
  | O => SVis (EUndef UFuel) (fun _ => bail)
  | S f =>
    (* [comment removed for export] *)
    try_avail sc st (fun st1 first =>
      if negb (first =? 0) then k st1 (ctz32 first) else
      (* [comment removed for export] *)
      alloc_group R lay (alloc_slot lay f) st1 sc req (fun st2 go =>
        match go with
        | None => k st2 (-1)
        | Some g =>
          let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
          queue (LActive sc) g st3 (fun st4 => k st4 0) bail
        end) bail) bail
  end.

Definition FUEL : nat := 64%nat.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition malloc_small_ctrl {R} (lay : layout_hook) (st : mstate) (n : Z) (k : mstate -> option (aptr * Z) -> M R) (bail : M R) : M R :=
  let sc := size_to_class n in
  (* [comment removed for export] *)
  let g := active st sc in
  (* [comment removed for export] *)
  let sc :=
    match g with
    | Some _ => sc
    | None =>
      if (4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st sc =? 0) then
        let usage1 := usage st (Z.lor sc 1) in
        let usage1 := match active st (Z.lor sc 1) with
                      | None => usage1 + 3
                      | Some _ => let ar := get_meta_rec st (default (0%N,-1) (active st (Z.lor sc 1))) in
                                  if (m_avail ar =? 0) && (m_freed ar =? 0) then usage1 + 3 else usage1
                      end in
        if usage1 <=? 12 then Z.lor sc 1 else sc
      else sc
    end in
  let g := active st sc in
  (* [comment removed for export] *)
  let mask := match g with Some gp => m_avail (get_meta_rec st gp) | None => 0 end in
  let first := lowbit mask in
  match g, negb (first =? 0) with
  | Some gp, true => k (upd_meta gp (m_set_avail (mask - first)) st) (Some (gp, ctz32 first))
  | _, _ =>
    (* [comment removed for export] *)
    alloc_slot lay FUEL st sc n (fun st1 idx =>
      if idx <? 0 then k st1 None
      else match active st1 sc with
           | Some gp => k st1 (Some (gp, idx))
           | None => SVis (EUndef UBadPtr) (fun _ => bail)
           end) bail
  end.

(* [comment removed for export] *)
Definition malloc_core (lay : layout_hook) (st : mstate) (n : Z) : M (mstate * option (aptr * Z)) :=
  let bail := ret (st, @None (aptr * Z)) in
  (* [comment removed for export] *)
  if size_overflows n then ret (st, None) else
  if MMAP_THRESHOLD <=? n then
    (* [comment removed for export] *)
    let needed := n + IB + UNIT in
    SVis (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
      if negb (mmap_answer_ok (live_ranges st) needed r) then bad_answer bail else
      if is_err r then ret (st, None) else
      let '(st1, rid) := new_region RKGroup r needed st in
      (* [comment removed for export] *)
      let st2 := step_seq st1 in
      alloc_meta st2 (fun st3 go =>
        match go with
        | None =>
          (* [comment removed for export] *)
          SVis (EMunmap r needed) (fun ru => if munmap_answer_ok ru then ret (drop_region rid st3, None) else bad_answer bail)
        | Some g =>
          (* [comment removed for export] *)
          let st4 := upd_meta g (fun mr =>
                       m_set_freed 0 (m_set_avail 0 (m_set_maplen ((needed + 4095) / 4096)
                       (m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (rid, 0)) mr))))))) st3 in
          let st5 := put_group (rid, 0) (Some g) (group_active_idx st4 (rid, 0)) (lh_hdr lay st4 (rid, 0)) in
          let st6 := add_slots g (rid, 0) (get_stride (get_meta_rec st5 g)) 1 st5 in
          let st7 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st6 in
          ret (st7, Some (g, 0))
        end) bail)
  else
    malloc_small_ctrl lay st n (fun st1 r => ret (st1, r)) bail.

(* [comment removed for export] *)
Definition malloc (st0 : mstate) (n : Z) : M (mstate * optr) :=
  let st := set_tick (N.succ (s_tick st0)) st0 in
  '(st1, r) <-- malloc_core full_lay st n ;;
  match r with
  | None => ret (st1, None)
  | Some (g, idx) =>
    (* [comment removed for export] *)
    enframe_full st1 g idx n (c_mmap_counter (ctx st1)) (fun st2 p => ret (havoc p n st2, Some p))
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition okay_to_free : ltac2:(zQ "30!oc!o5!jj5>2st$2>1g$1$0") := ltac2:(zQ "hc0!oc!uc!jb!u5!pi3!o5!t8!iga!hlc!nt4!nv5!pc!ih0!nr3!mk1!psf!qib!mm5!mnc!mo9!mpc!mq5!jg3!jj5!pq8!pj5!qj9!hg3\2st$h7\1g$5=2mr$h6@2$e^2^1=2sc$2@1$h5^1M0\0$0$0@2$6@1$h1^2Z$3M0\0$0$0@2$c@2$7+j0^1@2$8@1$f^2@2$9$d@1$h9^1$1M0\0$0$0@2$6@1$h3^2Z$1M0\0$0$0@1$4@2$h8@1$h4^2@2$a$5^3$1M0\0$0$0@1$4@2$h0^1^4$1=3cnt$2@2$hb@1$h2^2+1=3usg$2@2$ha^5^2M0\0$0$0@2$b@2$7@2$9+9^2^1@2$8^2+h4$1$3").

Definition mapinfo : ltac2:(zQ "00T") := ltac2:(zQ "40!jf!h8!jb!o5@1$0@2$1$3$2").   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition decoder : ltac2:(zQ "00>1RTT") := ltac2:(zQ "40!qk1!o5!jb!jj5\1RT>0$3>0$1>0>0$1>0$2@1$0^5>0@1$0^4@1$0^5").
Definition dec_hdr {R} : decoder R := fun st p k bail => get_meta st p (fun m _ idx => k m idx) bail.
Definition dec_slots {R} : decoder R := fun st p k bail =>
  match (s_slots st) !! p with
  | Some (m, idx) => k m idx
  | None => SVis (EUndef UBadPtr) (fun _ => bail)
  end.

Section FREE_GROUP.
Variable R : Type.
Variable dec : ltac2:(zQ "10!qr2@1$0?1R").
Variable nontrivial_free_rec : ltac2:(zQ "50!qk1!jj5!jb!o5!qk5>0$1>0$3>0$2>0>0$1>0$4@1$0?1R>0@1$0?1R@1$0?1R").

(* [comment removed for export] *)
Definition free_group : ltac2:(zQ "40!qk1!jj5!o5!qk5>2st$1>1g$2>1k>0$1>0$3@1$0?1R>4bail@1$0?1R@1$0?1R") := ltac2:(zQ "i20!jj5!jb!o5!oc!qk1!jf!qkf!mnc!mo9!qk5!hg3!nv5!pi3!vd!h8!qlb!qm4!qme!qna!hg9!mk1!psf!mp4!mq5!jg3!qo6!qp3!qpf!qj9!qqa!t8!hlc!nt4!hm2\2st$0\1g$2\1k>0$0>0$9@1$4?1R\4bail@1$4?1R=2mr$h8@2$h4^4^3=2sc$1@1$h7^1=3st1$0M3\0$3$0@2$hf^1+j0@3$ha^1@2$i1@2$hc^6^1@2$a@1$7^2+1^6^6M5\1x@1$5$2@1$4?1R@1$h6^3\1p$2=3st1$0@4$h2^1@1$h5^4@2$a@1$7^4+1@2$h1^1^2M3\0$3@1$4?1R@1$c@2$he@1$8^5Z=3st2$0@2$h9^4@1$hb^1@5$6?1R^9^1\3st3$0@2^9^1@2$b@2$e$2$1@4$d$2$1^4@2$i0@1$8^7+hgg0^7@4?3dec^1^2\1m$2\3idx$1@5?h3nontrivial_free_rec^3^2^1\3st3$0\2mi$9@5$6?1R^c^2\3st4$0@2^c^1^2^a^8^6@5$hd$h3$1?1R@1$f$h0\0$1^5").
End FREE_GROUP.

(* [comment removed for export] *)
Fixpoint nontrivial_free {R} (dec : decoder R) (fuel : nat) (st : mstate) (g : aptr) (i : Z) (k : mstate -> mapinfo -> M R) (bail : M R) {struct fuel} : M R :=
  match fuel with
  | O => SVis (EUndef UFuel) (fun _ => bail)
  | S f =>
    let mr := get_meta_rec st g in
    let self := bit i in
    let sc := m_sizeclass mr in
    let mask := Z.lor (m_freed mr) (m_avail mr) in
    if (mask + self =? mask_upto (m_last_idx mr)) && okay_to_free st g then
      (* [comment removed for export] *)
      match m_next mr with
      | Some _ =>
        guard 50 (sc <? 48) (
          let activate_new := optr_eqb (active st sc) (Some g) in
          let st1 := dequeue (LActive sc) g st in
          match activate_new, active st1 sc with
          | true, Some a => activate_group a st1 (fun st2 _ => free_group R dec (nontrivial_free dec f) st2 g k bail) bail
          | _, _ => free_group R dec (nontrivial_free dec f) st1 g k bail
          end) bail
      | None => free_group R dec (nontrivial_free dec f) st g k bail
      end
    else if mask =? 0 then
      (* [comment removed for export] *)
      guard 51 (sc <? 48) (
        let aor (st : mstate) := k (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) self) r) st) None in
        if negb (optr_eqb (active st sc) (Some g)) then queue (LActive sc) g st aor bail
        else aor st) bail
    else
      (* [comment removed for export] *)
      k (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) self) r) st) None
  end.

(* [comment removed for export] *)
Definition free_tail : ltac2:(zQ "50!jj5!jb!qk1!o5!qr2>3dec@1$4$0>2st$0>1g$3>3idx$1@1$2$0") := ltac2:(zQ "i60!jj5!jb!qrc!oc!o5!h8!qk1!pi3!t8!jf!hg9!hg3!p2!ih0!j7!qs2!qsc!qt3!qu0!ngc!qr2!qu6!mk1!qv4!mlb!mn2!mnc!qvc!qk5!rga!jg3!rh6!ria!rjc!po3!qqa!hkb!ps9\3dec@1$h4$0\2st$0\1g$4\3idx$1=2mr$he@2$h6^3^2=4self$1@1$h2^2=3all$1@1$hd@1$ha^2=5freed$1@1$h9^3=5avail$1@1$h8^4=4mask$1@2$i5^2^1@5$h7$0+jc@1$7@2$i1^1^7M3\0$3@1$6$0@1$7@2$d@2$8^3Z@2$8@2$b^1^5^4@2$2$0@3$i2^8@1$hb@2$b^3^5^9@8$i0$0^a$h0^9^8^7\3st2$0\2mi$hcM9\2mi@1$9@2$5$4$1@1$6$0^1\1p@2$5$4$1M5\1p@2$5$4$1@1$6$0^1\4base$4\3len$1M3\0$3@1$6$0@1$7@2$8^1Z@5$i3$a$1$0@2$f@2$h3^5^2^1\2ru$1M3\0$3@3$i4$a$1$0@1$hf^1@2$2$0@2$h5@3$c$e$1^3^6@2$h1$0@2$2$0^f@2$2$0^5@2$2$0^2@2$2$0^9@2$2$0^9").

(* [comment removed for export] *)
Definition free_hdr : ltac2:(zQ "60!h8!o5!jj5!jf!jb!qk1>2st$2>1p$1@1$5@1$3@2$0@2$0$2$1$4") := ltac2:(zQ "h90!h8!o5!jb!jj5!jf!nra!vd!qk1!qrc!jga!nv5!qlb!pk2!qm4!hg9!rk6!mk1!rl1!psf!jg3!rm5!rn2!om5!qqa!hm2\2st$3\1p$1=4bail@1$7@1$4@2$0@2$0$3$1$2@2$8@1$4@2$0@2$0$3$1$2@1$9@2$0@2$0$3$1$2@5$f@1$4@2$0@2$0$3$1$2^3^2\1g$1\0$2\3idx$2=2mr$h3@2$h0^6^3M4\1x@1$4$1@1$7@1$4@2$0@2$0$3$1$2@2$h4^1^2\5start$1=1e$1@2$5^1@2$h8@1$h2^2$c@6$h1@1$4@2$0@2$0$3$1$2^9^8^1\0$2=3st1$3@3$h5@2$5^9-2Z@3$h6@2$5^9-3+vf^a@2$8@1$4@2$0@2$0$3$1$2@2$a@2$0@2$0$3$1$2@4$6@2$0$3$1$2@4$6$3$1^1^8^6^7@5$h7$e$2@1$4@2$0@2$0$3$1$2@1$b$d\0$2^6^1").

(* [comment removed for export] *)
Definition free : ltac2:(zQ "30!jj5!qk1!te>2st$0>1p$2@1$1$0") := ltac2:(zQ "e0!jj5!h8!jb!o5!jf!hg9!hkb!qrc!qk1!rn9!ro3!roe!te!rpa\2st$0\1p$cM4\1p@1$4$3@1$8$0^1\1p$3@6$d$5$2@1$4@2$1@2$1$0$3$2$0@2$a^3^1\1r@1$4@2$1@2$1$0$3$2M4\1r@1$4@2$1@2$1$0$3$2@3$6$5$2$0^1\2p0@2$1@2$1$0$3$2M1\2p0@2$1@2$1$0$3$2@3$6$5$2$0^1\2p1@2$1$0$3\3idx$2M1\2p1@2$1$0$3@3$6$5$2$0^2\3st1$0\1g$3@4$b@1$9$0^2^1^3@2$7$0^4@2$7$0^2").

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cptr : ltac2:(zQ "00T") := ltac2:(zQ "10!o5$0").

Definition strip : ltac2:(zQ "10!jj5>2st$0$0") := ltac2:(zQ "h30!j7!ind!jl9!jkf!jpa!jrd!jj5!js7!jt1!jt9!ju4!jue!jvb!kg7!kh4!kia!isd!iu2!iua\2st$6@b$5@1$8^1@1$c^1@2$h0@4$h1$0$3$2$1@4$h2$0$3$2$1@1$b^1@1$a^1@1$7^1@1$9^1@1$f^1$4@1$e^1@1$d^1").

Definition cmalloc (cs : mstate) (n : Z) : M (mstate * option cptr) :=
  '(st1, r) <-- malloc_core lay_none cs n ;;
  ret (strip st1, match r with Some (g, idx) => Some (slot_of st1 g idx) | None => None end).

Definition cfree (cs : mstate) (p : option cptr) : M mstate :=
  match p with
  | None => ret cs
  | Some s =>
    match (s_slots cs) !! s with
    | None => SVis (EUndef UBadPtr) (fun _ => ret cs)
    | Some (g, idx) => '(st1) <-- free_tail dec_slots cs g idx ;; ret (strip st1)
    end
  end.
