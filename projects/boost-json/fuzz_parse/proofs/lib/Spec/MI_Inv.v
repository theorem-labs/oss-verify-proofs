(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc KInv.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~04aptr04meta06mstate0cget_meta_rec37Corelib7Numbers7BinNumsm01Z0am_last_idx46Stdlib6ZArith6BinInt1Zo93addm01N37Corelib4Init9Datatypesqb4prodqb2idqb4pairm02N005m_mem25stdpp6optionu2bfrom_optionqb3snd79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Inv~~~~~~hg45gbase04UNIT0aget_strideo93mulhg46cnt_ofhg46sstartqb3fst37Corelib4Init5Logichnd2eq0bslot_start'04ghdr35stdpp7numbers1Nhqa6eq_dec35stdpp7numbers1Zhs56eq_decqb4Some25stdpp9countablehu7bN_countablehu7bZ_countablehu7eprod_countable25stdpp9decidableii8bprod_eq_decqb6optionhnd2ex06mkGhdr08s_groups25stdpp4baseim96lookup25stdpp4gmapinf4gmapinfbgmap_lookuphg45hosts04cptrhg43blkqb4boolo97testbit07m_avail07m_freed09mask_uptoo93lorqb4list36Stdlib5Lists4Listiv3afold_righthg42MR37Corelib5Lists7ListDefjha3maphg44zsum06g_meta0bm_sizeclasso93eqb25stdpp8fin_mapsjlbbmap_to_listinf9gmap_fold06region05r_len0h2c_avail_meta_areas05s_ctx46Stdlib6NArith6BinNat1Njr23eqb06r_kind05rkindhnd2or05RKBrk06RKMeta08AREA_HDR09META_SIZE04aaddqb3appqb4consqb3nilhnd4Truehg46linked04optrqb4Nonehg46extrashg43mkXhnd3andhnd3not05lheadiv32In06shadow0aget_shadow89OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Inv3INV~~~~~~ko23SHd05Known09cell_read07cellval07Unknowno94lando96shiftrko25inv_Ako25inv_Gko25inv_Lko25inv_Mko25inv_Rko25inv_Sko26inv_SH79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4KInv~~~~~~ljf4mledhg44INVL04mctx" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition MR : ltac2:(zQ "30!je!k4!ka>2st$2>1m$0$1") := ltac2:(zQ "30!je!l2!ka\2st$2\1m$0@2$1^2^1").
Definition cnt_of : ltac2:(zQ "20!n9!k4>1r$1$0") := ltac2:(zQ "30!nd!k4!q1\1r$1@2$2@1$0^1+1").
(* [comment removed for export] *)
Definition gbase : ltac2:(zQ "20!je!k4>1r$1$0") := ltac2:(zQ "90!q7!n9!s3!sa!sf!t6!tb!k4!v0\1r$7@5$8@2$2$0$1@2$2$0$1@1$3@2$2$0$1@4$4$0$1$5Z@1$6^1").
(* [comment removed for export] *)
Definition sstart : ltac2:(zQ "20!n9!k4>1r$1>1i$0$0") := ltac2:(zQ "90!n9!q1!ve!q7!hk2!hkb!hl1!k4!hld\1r$7\1i$0@2$1@2$1@3$2$3$0@1$4^2$5@2$8@1$6^2^1").
Definition gend : ltac2:(zQ "20!n9!k4>1r$1$0") := ltac2:(zQ "30!hm3!hmd!k4\1r$2@2$1^1@1$0^1").

Lemma slot_start'_sstart : ltac2:(zQ "a0!n9!q7!hn7!sf!hp1!hk2!hmd!je!k4!hp7>1r$8>1i$0@3$4$7@2$9^2^1@4$3$1$0@3$2$1$0@1$5^2@2$6^2^1").
Proof. intros r i. unfold slot_start', sstart, gbase, aadd. destruct (m_mem r) as [[? ?]|]; cbn; f_equal; lia. Qed.

(* [comment removed for export] *)
Definition hosts : ltac2:(zQ "20!je!ka>2st$1>1b$0>1m$0P") := ltac2:(zQ "h40!n9!je!hq4!q7!hrb!ht6!hu0!hv8!ig7!ih6!ij9!ik8!hp1!il1!il7!ka!ilf!in5!iob!ip3\2st$f\1b$1\1m$1@2$d$0\2ai$0@3$c@1$b$2@6$h1$1$2@4$h2$1@4$a$3$4$0$5@6$9$3$4$7$0$5$8$2@4$h3$1@4$a$3$4$0$5@6$9$3$4$7$0$5$8$2^3@1$h0^4@2$6$2@2$e@2$6$1^2^1").
Definition live_group : ltac2:(zQ "20!je!ka>2st$1>1m$0P") := ltac2:(zQ "40!je!il1!iq2!ka\2st$3\1m$0@2$1$0\1b$0@3$2^3^1^2").

(* [comment removed for export] *)
Definition blk : ltac2:(zQ "00T") := ltac2:(zQ "30!s3!n9!iqb@2$0@2$0$2$1$1").
Definition bslot : ltac2:(zQ "20!ir1!iqb>1b$0$1") := ltac2:(zQ "50!n9!hn7!iqb!s3!ir1\1b$4@3$1$2$0@3$1@2$3$2$0$0^1").
Definition boff : ltac2:(zQ "20!n9!ir1>1b$1$0") := ltac2:(zQ "60!n9!iqb!hn7!s3!ve!ir1\1b$5@3$4$1$0@3$2@2$3$1$0$0^1").
Definition bsize : ltac2:(zQ "20!n9!ir1>1b$1$0") := ltac2:(zQ "50!n9!s3!ve!ir1!iqb\1b$3@3$2@2$1$4$0$0^1").
(* [comment removed for export] *)

Fixpoint bl_remove (c : cptr) (l : list blk) : list blk :=
  match l with
  | [] => []
  | b :: l' => if aptr_eqb (bslot b) c then l' else b :: bl_remove c l'
  end.

Definition tbit : ltac2:(zQ "20!n9!ir8>1m$0>1i$0$1") := ltac2:(zQ "20!n9!irf\1m$0\1i$0@2$1^2^1").
(* [comment removed for export] *)
Definition allfree : ltac2:(zQ "10!k4>1r$0P") := ltac2:(zQ "80!hp1!n9!is9!it2!nd!itb!k4!iu6\1r$6@3$0$1@2$7@1$2^1@1$3^1@1$5@1$4^1").

Definition zsum : ltac2:(zQ "20!n9!iuc>1l@1$1$0$0") := ltac2:(zQ "40!n9!iuc!jg6!q1\1l@1$1$0@5$2$0$0$3Z^1").
(* [comment removed for export] *)
Definition gcnt : ltac2:(zQ "20!n9!ka>2st$1>2sc$0$0") := ltac2:(zQ "ha0!n9!je!hq4!q7!hrb!ht6!ir8!ik8!s3!jh4!hv8!ig7!ih6!ij9!ve!jj1!hm3!jj8!jk0!jk8!ka!ilf!jl5!jmb!iob!jna\2st$h4\2sc$0@1$h1@4$f@2$8$1$2$0\2bh@2$8$1$2M7\1x@1$7$1$0@1$h2@3$e$1$2^1\1m$1M6\0$6$0@2$h6@1$h3@2$9^4^1^3@1$h0@2$9^4^1ZZ@5$h7$1$2@4$h8$1@4$d$3$4$0$5@6$c$3$4$a$0$5$b$2@4$h9$1@4$d$3$4$0$5@6$c$3$4$a$0$5$b$2@1$h5^2").

(* [comment removed for export] *)
Definition frontier : ltac2:(zQ "40!q7!n9!ka!jo7>2st$2>3rid$0>1r$3$1") := ltac2:(zQ "c0!n9!q7!ir8!ik8!s3!je!jof!jp6!ka!jo7!jqb!jsa\2st$8\3rid$1\1r$9M3\1x@1$3$5$0@1$7@1$a^3\1a$5M4\1a@2$4$1$0$0^1\4rid0$1\4off0$0M2\0$2$0@2$b^2^5^1@1$6^4@1$6^1").

Definition is_metakind : ltac2:(zQ "10!jo7>1r$0P") := ltac2:(zQ "70!hp1!jt1!jt9!ju0!ju6!jud!jo7\1r$6@2$3@3$0$2@1$1^1$4@3$0$2@1$1^1$5").

(* [comment removed for export] *)
Definition mslot : ltac2:(zQ "20!je!n9>1a$0>1k$1$0") := ltac2:(zQ "70!n9!jv5!jvf!kga!je!q1!hld\1a$4\1k$0@2$3^2@2$5$1@2$6$2^1").

(* [comment removed for export] *)
Fixpoint linked (st : mstate) (l : list aptr) : Prop :=
  match l with
  | x :: ((y :: _) as t) => m_next (MR st x) = Some y /\ m_prev (MR st y) = Some x /\ linked st t
  | _ => True
  end.
Definition dll : ltac2:(zQ "30!iuc!je!ka>2st$2>1l@1$0$1P") := ltac2:(zQ "80!je!iuc!kh0!kh6!khd!ki3!kib!ka\2st$7\1l@1$1$0M1\1l@1$1$0P^1$5\1a$0\2l0@1$1$0@2$6^4@3$2$0^3@3$3$0^2@1$4$0").
Definition head_of : ltac2:(zQ "30!iuc!je!kj5>1l@1$0$1$2") := ltac2:(zQ "50!je!iuc!kjb!hu0!kj5\1l@1$1$0M1\1l@1$1$0$4^1@1$2$0\1m$0\2l0@1$1$0@2$3$0^2").

(* [comment removed for export] *)
Record extras : Type := mkX {
  x_idle : list aptr;        (* [comment removed for export] *)
  x_zomb : list aptr;        (* [comment removed for export] *)
  x_pend : option aptr;      (* [comment removed for export] *)
  x_orph : option N;         (* [comment removed for export] *)
  x_fresh : option aptr      (* [comment removed for export] *)
}.
Definition x0 : ltac2:(zQ "10!kk2$0") := ltac2:(zQ "50!je!kjb!khd!q7!kkc@5$4@1$2$0@1$2$0@1$1$0@1$1$3@1$1$0").

(* [comment removed for export] *)
Definition one5 : ltac2:(zQ "00>1AP>1BP>1CP>1DP>1EPP") := ltac2:(zQ "30!kl3!kla!ju0\1AP\1BP\1CP\1DP\1EP@2$0@2$2^5@2$2^4@2$2^3@2$2^2^1@2$0@1$1@2$0^5^4@2$0@1$1@2$0^5^3@2$0@1$1@2$0^5^2@2$0@1$1@2$0^5^1@2$0@1$1@2$0^4^3@2$0@1$1@2$0^4^2@2$0@1$1@2$0^4^1@2$0@1$1@2$0^3^2@2$0@1$1@2$0^3^1@1$1@2$0^2^1").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section INV.
Variable X : ltac2:(zQ "10!kk2$0").
Variable st : ltac2:(zQ "10!ka$0").
Variable L : ltac2:(zQ "10!lnb$0").
Variable BL : ltac2:(zQ "20!iuc!ir1@1$0$1").
Variable LS : ltac2:(zQ "30!iuc!je!km1>0$2@1$0$1").       (* [comment removed for export] *)
Let cx : ltac2:(zQ "10!lob$0") := ltac2:(zQ "10!jqb@1$0?2st").
Let R : ltac2:(zQ "20!je!k4>1m$0$1") := ltac2:(zQ "10!jh4@1$0?2st").
Definition in_list : ltac2:(zQ "10!je>1m$0P") := ltac2:(zQ "40!je!km1!il1!km8\1m$0@2$2$1\1h$1@3$3$0^2@1?2LS^1").

(* [comment removed for export] *)
Record inv_R : Prop := mkIR {
  ir_ids : forall rid r, s_regions st !! rid = Some r -> (rid < s_next_rid st)%N;
  ir_shape : forall rid r, s_regions st !! rid = Some r ->
      0 < r_base r /\ r_base r mod PGSZ = 0 /\ 0 < r_len r /\ r_len r < LEN_MAX
      /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
      /\ (is_metakind r -> r_len r mod PGSZ = 0 /\ 2 * PGSZ <= r_len r);
  ir_disj : forall rid1 rid2 r1 r2, s_regions st !! rid1 = Some r1 -> s_regions st !! rid2 = Some r2 -> rid1 <> rid2 ->
      let '(b1, l1) := region_live_range r1 in let '(b2, l2) := region_live_range r2 in
      b1 + l1 <= b2 \/ b2 + l2 <= b1;
  ir_resv : ld_resv L = s_reserved st;
  ir_groups : Permutation (ld_groups L)
      (map (fun kr => (r_base (snd kr), r_len (snd kr)))
           (List.filter (fun kr => match r_kind (snd kr) with RKGroup => true | _ => false end) (map_to_list (s_regions st))));
  ir_metas : Permutation (ld_metas L)
      (map (fun kr => (r_base (snd kr), r_len (snd kr), frontier st (fst kr) (snd kr) / PGSZ - 1))
           (List.filter (fun kr => match r_kind (snd kr) with RKMeta => true | _ => false end) (map_to_list (s_regions st))));
  ir_metalen : forall rid r, s_regions st !! rid = Some r -> r_kind r = RKMeta ->
      (exists j, 1 <= j /\ r_len r = 2^j * PGSZ)
      /\ PGSZ <= frontier st rid r <= r_len r /\ frontier st rid r mod PGSZ = 0;
  ir_brkfront : forall rid r, s_regions st !! rid = Some r -> r_kind r = RKBrk -> frontier st rid r = r_len r;
  ir_shift : 0 <= c_meta_alloc_shift cx /\
      (c_meta_alloc_shift cx = 0 \/
       exists rid r, s_regions st !! rid = Some r /\ r_kind r = RKMeta /\ r_len r = 2^(c_meta_alloc_shift cx) * PGSZ);
  ir_brkreg : forall b l, ld_brkreg L = Some (b, l) <->
      exists rid r, s_regions st !! rid = Some r /\ r_kind r = RKBrk /\ r_base r = b /\ r_len r = l;
  ir_brk1 : forall rid1 rid2 r1 r2, s_regions st !! rid1 = Some r1 -> s_regions st !! rid2 = Some r2 ->
      r_kind r1 = RKBrk -> r_kind r2 = RKBrk -> rid1 = rid2;
  ir_brk : match c_brk cx with
      | BrkUntried => ld_brk L = BPUntried /\ forall rid r, s_regions st !! rid = Some r -> r_kind r <> RKBrk
      | BrkLive rid off => ld_brk L = BPLive /\
          exists r, s_regions st !! rid = Some r /\ r_kind r = RKBrk /\ r_len r = off
      | BrkDead => ld_brk L = BPDead
      end;
  (* [comment removed for export] *)
  ir_cursor : 0 <= c_avail_meta_area_count cx /\
      (0 < c_avail_meta_area_count cx -> c_avail_meta_areas cx <> None) /\
      (forall rid off, c_avail_meta_areas cx = Some (rid, off) ->
       exists r, s_regions st !! rid = Some r /\ is_metakind r /\ PGSZ <= off /\ off mod PGSZ = 0
         /\ off + c_avail_meta_area_count cx * PGSZ = r_len r
         /\ (0 < c_avail_meta_area_count cx -> r_kind r = RKMeta));
  (* [comment removed for export] *)
  ir_orph : forall rid, x_orph X = Some rid ->
      exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup /\ forall b, fst b = rid -> s_groups st !! b = None;
  (* [comment removed for export] *)
  ir_pages : forall rid r q, s_regions st !! rid = Some r -> is_metakind r -> 1 <= q -> (q + 1) * PGSZ <= frontier st rid r ->
      x_fresh X <> Some (rid, q * PGSZ) -> s_areas st !! (rid, q * PGSZ) <> None;
  (* [comment removed for export] *)
  ir_mshift : (forall rid r, s_regions st !! rid = Some r -> r_kind r = RKMeta ->
                 exists j, 1 <= j <= c_meta_alloc_shift cx /\ r_len r = 2^j * PGSZ)
      /\ (forall rid1 rid2 r1 r2, s_regions st !! rid1 = Some r1 -> s_regions st !! rid2 = Some r2 ->
            r_kind r1 = RKMeta -> r_kind r2 = RKMeta -> r_len r1 = r_len r2 -> rid1 = rid2)
      /\ (forall j, 1 <= j <= c_meta_alloc_shift cx ->
            exists rid r, s_regions st !! rid = Some r /\ r_kind r = RKMeta /\ r_len r = 2^j * PGSZ)
}.

(* [comment removed for export] *)
Record inv_A : Prop := mkIA {
  ia_ctx : 0 <= c_mmap_counter cx < 2^32 /\ 0 <= c_seq cx < 256
      /\ (forall i v, c_bounces cx !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256)
      /\ (forall i v, c_unmap_seq cx !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256);
  ia_secret : 0 <= s_secret st < 2^64 /\
      ((c_init_done cx = 0 /\ c_secret cx = 0 /\ s_areas st = ∅) \/ (c_init_done cx = 1 /\ c_secret cx = s_secret st));
  (* [comment removed for export] *)
  ia_areas : forall a ar, s_areas st !! a = Some ar ->
      (exists r, s_regions st !! (fst a) = Some r /\ is_metakind r /\ snd a mod PGSZ = 0 /\ PGSZ <= snd a
                 /\ snd a + PGSZ <= frontier st (fst a) r)
      /\ a_check ar = c_secret cx /\ a_nslots ar = NSLOTS
      /\ (forall a', a_next ar = Some a' -> s_areas st !! a' <> None);
  ia_head : forall h, c_meta_area_head cx = Some h -> s_areas st !! h <> None;
  ia_tail : forall t, c_meta_area_tail cx = Some t -> s_areas st !! t <> None;
  ia_tail0 : c_meta_area_tail cx = None -> s_areas st = ∅ /\ c_avail_meta_count cx = 0;
  (* [comment removed for export] *)
  ia_metas : forall m mr, s_metas st !! m = Some mr ->
      exists a ar k, s_areas st !! a = Some ar /\ 0 <= k < NSLOTS /\ m = mslot a k;
  (* [comment removed for export] *)
  ia_avail : 0 <= c_avail_meta_count cx <= NSLOTS /\
      (0 < c_avail_meta_count cx ->
       exists a, c_meta_area_tail cx = Some a /\
         c_avail_meta cx = Some (mslot a (NSLOTS - c_avail_meta_count cx)) /\
         forall k, NSLOTS - c_avail_meta_count cx <= k < NSLOTS -> s_metas st !! (mslot a k) = None);
  ia_availptr : forall q, c_avail_meta cx = Some q ->
      exists r, s_regions st !! (fst q) = Some r /\ is_metakind r;
  (* [comment removed for export] *)
  ia_usage : forall sc, 0 <= sc < 48 -> usage st sc = gcnt st sc;
  ia_usage_keys : forall sc v, c_usage cx !! sc = Some v -> 0 <= sc < 48;
  ia_active_keys : forall sc g, c_active cx !! sc = Some g -> 0 <= sc < 48;
  (* [comment removed for export] *)
  ia_carved : forall a ar k, s_areas st !! a = Some ar -> 0 <= k < NSLOTS ->
      (c_meta_area_tail cx = Some a -> k < NSLOTS - c_avail_meta_count cx) -> s_metas st !! (mslot a k) <> None
}.

(* [comment removed for export] *)
Record inv_M : Prop := mkIM {
  im_zero : forall m, m_mem (R m) = None ->
      R m = mkMeta (m_prev (R m)) (m_next (R m)) None 0 0 0 0 0 0;
  im_group : forall m b, m_mem (R m) = Some b -> hosts st b m \/ In m (x_zomb X);
  im_hdr : forall b h, s_groups st !! b = Some h ->
      exists m, g_meta h = Some m /\ m_mem (R m) = Some b /\ 0 <= g_active_idx h <= m_last_idx (R m);
  im_idle : forall m, In m (x_idle X) -> s_metas st !! m = Some meta0 /\ ~ in_list m;
  im_zomb : forall z, In z (x_zomb X) ->
      ~ in_list z /\ m_next (R z) = None /\ m_prev (R z) = None /\
      exists b, m_mem (R z) = Some b /\ s_groups st !! b = None;
  (* [comment removed for export] *)
  im_all : forall m, s_metas st !! m <> None -> live_group st m \/ in_list m \/ In m (x_idle X) \/ In m (x_zomb X)
}.

(* [comment removed for export] *)
Record inv_L : Prop := mkIL {
  il_head : forall h, get_head st h = head_of (LS h);
  il_dll : forall h, dll st (LS h);
  il_nodup : forall h, NoDup (LS h);
  il_disj : forall h1 h2 m, In m (LS h1) -> In m (LS h2) -> h1 = h2;
  il_link : forall m, (in_list m <-> m_next (R m) <> None) /\ (m_next (R m) = None -> m_prev (R m) = None);
  il_free : forall m, In m (LS LFree) -> R m = mkMeta (m_prev (R m)) (m_next (R m)) None 0 0 0 0 0 0;
  il_active : forall sc m, In m (LS (LActive sc)) -> 0 <= sc < 48 /\ live_group st m /\ m_sizeclass (R m) = sc;
  (* [comment removed for export] *)
  il_keys : forall h, LS h <> [] -> match h with LFree => True | LActive sc => 0 <= sc < 48 end
}.

(* [comment removed for export] *)
Record group_ok (m b : aptr) (ai : Z) : Prop := mkG {
  g_present : s_metas st !! m <> None;
  g_li : 0 <= m_last_idx (R m) <= 31;
  g_ai : 0 <= ai <= m_last_idx (R m);
  g_sc : (0 <= m_sizeclass (R m) < 48 /\ m_maplen (R m) <= 256)
         \/ (m_sizeclass (R m) = 63 /\ m_last_idx (R m) = 0 /\ m_maplen (R m) <> 0 /\ ~ in_list m);
  g_freeable : m_freeable (R m) = 1;
  g_maplen : 0 <= m_maplen (R m);
  g_masks : 0 <= m_avail (R m) /\ 0 <= m_freed (R m)
      /\ (forall i, 0 <= i -> tbit (m_avail (R m)) i = true -> i <= ai)
      /\ (forall i, 0 <= i -> tbit (m_freed (R m)) i = true -> i <= m_last_idx (R m))
      /\ (forall i, 0 <= i -> tbit (m_avail (R m)) i = true -> tbit (m_freed (R m)) i = true -> False)
      /\ (forall i, ai < i <= m_last_idx (R m) -> tbit (m_freed (R m)) i = true);
  (* [comment removed for export] *)
  g_partial : x_fresh X <> Some m -> ai < m_last_idx (R m) -> In m (LS (LActive (m_sizeclass (R m))));
  g_unlisted : x_fresh X <> Some m -> m_sizeclass (R m) < 48 -> ~ in_list m -> m_avail (R m) = 0 /\ m_freed (R m) = 0;
  g_rest : x_fresh X <> Some m -> forall sc, In m (LS (LActive sc)) -> Some m <> head_of (LS (LActive sc)) ->
      m_avail (R m) = 0 /\ m_freed (R m) <> 0;
  (* [comment removed for export] *)
  g_stride : m_sizeclass (R m) < 48 ->
      (get_stride (R m) <= UNIT * size_class (m_sizeclass (R m)) \/ 28 <= m_sizeclass (R m))
      /\ (m_last_idx (R m) = 0 -> m_maplen (R m) <> 0 /\ 27 <= m_sizeclass (R m))
      /\ get_stride (R m) * cnt_of (R m) < 2^20;
  g_under : x_fresh X <> Some m -> m_sizeclass (R m) < 48 -> get_stride (R m) < UNIT * size_class (m_sizeclass (R m)) ->
      m_avail (R m) = 0 /\ m_freed (R m) = 0;
  g_align : 0 <= snd b /\ snd b mod UNIT = 0;
  (* [comment removed for export] *)
  g_top : m_maplen (R m) <> 0 ->
      snd b = 0 /\ exists r, s_regions st !! (fst b) = Some r /\ r_kind r = RKGroup
        /\ m_maplen (R m) * 4096 = round_up_pg (r_len r) /\ gend (R m) <= m_maplen (R m) * 4096;
  g_nest : m_maplen (R m) = 0 ->
      exists p i, s_slots st !! b = Some (p, i) /\ fst (gbase (R p)) = fst b
        /\ gend (R m) <= sstart (R p) i + get_stride (R p)
        /\ m_sizeclass (R m) < m_sizeclass (R p) < 48
        /\ get_stride (R p) = UNIT * size_class (m_sizeclass (R p));
  (* [comment removed for export] *)
  g_full0 : m_sizeclass (R m) = 0 -> ai = m_last_idx (R m);
  (* [comment removed for export] *)
  g_big0 : m_sizeclass (R m) = 63 -> m_avail (R m) = 0 /\ m_freed (R m) = 0
}.

Record inv_G : Prop := mkIG {
  ig_ok : forall m b ai, s_groups st !! b = Some (mkGhdr (Some m) ai) -> group_ok m b ai;
  ig_nometa : forall b ai, s_groups st !! b = Some (mkGhdr None ai) -> False;
  ig_onepartial : forall m1 m2 b1 b2 ai1 ai2,
      s_groups st !! b1 = Some (mkGhdr (Some m1) ai1) -> s_groups st !! b2 = Some (mkGhdr (Some m2) ai2) ->
      ai1 < m_last_idx (R m1) -> ai2 < m_last_idx (R m2) -> m_sizeclass (R m1) = m_sizeclass (R m2) -> m1 = m2;
  (* [comment removed for export] *)
  ig_top : forall rid r, s_regions st !! rid = Some r -> r_kind r = RKGroup -> x_orph X <> Some rid ->
      exists m, hosts st (rid, 0) m /\ m_maplen (R m) <> 0;
  (* [comment removed for export] *)
  ig_region : forall b h, s_groups st !! b = Some h -> exists r, s_regions st !! (fst b) = Some r /\ r_kind r = RKGroup;
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  ig_oneempty : forall m1 m2 b1 b2 ai1 ai2,
      s_groups st !! b1 = Some (mkGhdr (Some m1) ai1) -> s_groups st !! b2 = Some (mkGhdr (Some m2) ai2) ->
      m_sizeclass (R m1) < 48 -> m_sizeclass (R m2) = m_sizeclass (R m1) ->
      allfree (R m1) -> allfree (R m2) -> m1 = m2
}.

(* [comment removed for export] *)
Record inv_S : Prop := mkIS {
  is_valid : forall s m i, s_slots st !! s = Some (m, i) ->
      live_group st m /\ 0 <= i <= m_last_idx (R m) /\ s = slot_start' (R m) i;
  is_total : forall b m i, hosts st b m -> 0 <= i <= m_last_idx (R m) ->
      s_slots st !! (slot_start' (R m) i) = Some (m, i);
  is_part : forall b m ai i, s_groups st !! b = Some (mkGhdr (Some m) ai) -> 0 <= i <= m_last_idx (R m) ->
      let s := slot_start' (R m) i in
      one5 (tbit (m_avail (R m)) i = true)
           (tbit (m_freed (R m)) i = true)
           (In s (map bslot BL))
           (s_groups st !! s <> None)
           (x_pend X = Some s);
  is_pend : forall s, x_pend X = Some s -> s_slots st !! s <> None;
  (* [comment removed for export] *)
  is_nodup : NoDup (map bslot BL);
  is_blocks : forall k, In k BL ->
      exists m i, s_slots st !! (bslot k) = Some (m, i)
        /\ 0 <= boff k <= 255 /\ 0 <= bsize k /\ UNIT * boff k + bsize k <= get_stride (R m) - IB;
  (* [comment removed for export] *)
  is_big : forall k m i, In k BL -> s_slots st !! (bslot k) = Some (m, i) -> m_sizeclass (R m) = 63 ->
      exists r, s_regions st !! (fst (bslot k)) = Some r /\ r_kind r = RKGroup /\ r_len r = bsize k + IB + UNIT
}.

(* [comment removed for export] *)
Definition SHd : ltac2:(zQ "20!q7!kme>3rid$0$1") := ltac2:(zQ "20!q7!kn6\3rid$0@2$1?2st^1").
Definition known : ltac2:(zQ "20!n9!je>1p$1>1v$0P") := ltac2:(zQ "a0!n9!q7!hn7!ve!hp1!ks4!ksb!je!kt2!ktd\1p$7\1v$0@3$4$9@2$8@1$5@3$2$1$0^2@3$3$1$0^2@1$6^1").
Definition unknown : ltac2:(zQ "10!je>1p$0P") := ltac2:(zQ "b0!n9!q7!hn7!ve!hp1!il1!ks4!ku6!je!kt2!ktd\1p$8@2$5$0\1h$0@3$4$a@2$9@1$6@3$2$1$0^2@3$3$1$0^2@1$7^1").
Definition byte_of : ltac2:(zQ "10!n9>1x$0>1k$0$0") := ltac2:(zQ "40!n9!kuf!hld!kv6\1x$0\1k$0@2$1@2$3^2@2$2+8^1+vf").

Record inv_SH : Prop := mkISH {
  ish_dom : forall rid sh, s_shadow st !! rid = Some sh -> exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup;
  ish_ticks : forall rid sh, s_shadow st !! rid = Some sh ->
      (forall o v t, r_cells sh !! o = Some (v, t) -> 0 <= v < 256 /\ (t <= s_tick st)%N)
      /\ (forall u hl ch, r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= s_tick st)%N)
      /\ (forall pg t, r_havp sh !! pg = Some t -> (t <= s_tick st)%N);
  (* [comment removed for export] *)
  ish_hdr0 : forall b m i, hosts st b m -> 0 <= i <= cnt_of (R m) -> known (fst b, sstart (R m) i - IB) 0;
  (* [comment removed for export] *)
  ish_ghdr : forall b m o, hosts st b m -> 0 <= o < 12 -> unknown (fst b, snd b + o);
  (* [comment removed for export] *)
  ish_nest : forall b m p i, hosts st b m -> m_maplen (R m) = 0 -> s_slots st !! b = Some (p, i) ->
      let q := (snd b - snd (gbase (R p)) - UNIT) / UNIT in
      (exists v3, known (fst b, snd b - 3) v3 /\ Z.land v3 31 = i /\ 0 <= v3 < 256)
      /\ known (fst b, snd b - 2) (byte_of q 0) /\ known (fst b, snd b - 1) (byte_of q 1) /\ 0 <= q < 2^16;
  (* [comment removed for export] *)
  ish_blk : forall k m i, In k BL -> s_slots st !! (bslot k) = Some (m, i) ->
      let rid := fst (bslot k) in
      let p := snd (bslot k) + UNIT * boff k in
      let e := snd (bslot k) + get_stride (R m) - IB in
      let res := e - p - bsize k in
      let q := (p - snd (gbase (R m)) - UNIT) / UNIT in
      known (rid, p - 4) 0
      /\ known (rid, p - 3) (i + 32 * Z.min res 5)
      /\ known (rid, p - 2) (byte_of q 0) /\ known (rid, p - 1) (byte_of q 1) /\ 0 <= q < 2^16
      /\ (5 <= res -> known (rid, e - 4) (byte_of res 0) /\ known (rid, e - 3) (byte_of res 1)
                    /\ known (rid, e - 2) (byte_of res 2) /\ known (rid, e - 1) (byte_of res 3)
                    /\ known (rid, e - 5) 0 /\ res < 2^32)
      /\ (0 < res -> known (rid, e - res) 0)
      /\ (forall a, p <= a < p + bsize k -> unknown (rid, a))
}.

Definition INVL : ltac2:(zQ "00P") := ltac2:(zQ "80!kl3!kvf!lg8!lh1!lha!li3!lic!lj5@2$0$5@2$0$1@2$0$4@2$0$3@2$0$2@2$0$6$7").
End INV.

Definition INV : ltac2:(zQ "50!iuc!lnb!ir1!kk2!ka>1X$3>2st$4>1L$1>2BL@1$0$2P") := ltac2:(zQ "90!iuc!je!km1!il1!lnb!lo3!ir1!kk2!ka\1X$7\2st$8\1L$4\2BL@1$0$6@2$3>0$2@1$0$1\2LS>0$2@1$0$1@5$5^5^4^3^2^1").

(* [comment removed for export] *)
(* [comment removed for export] *)
