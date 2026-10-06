use vstd::prelude::*;
// Ghost-kode: findes kun når Verus kører, ikke ved en almindelig cargo build.
#[cfg(verus_only)]
use vstd::std_specs::bits::*;


verus! {

pub const WORDS: usize = 16384;
pub const MAX_FRAMES: usize = 1048576;

pub open spec fn bit_set(w: u64, k: u64) -> bool {
    (w >> k) & 1u64 == 1u64
}

// At sætte bit b ændre kun bit b
proof fn lemma_set_bit(w: u64, b: u64, k: u64)
        requires b < 64, k < 64,
        ensures bit_set(w | (1u64 << b), k) == (k == b || bit_set(w, k)),
{
    assert(((w | (1u64 << b)) >> k) & 1u64 == 1u64 <==> ((k == b) || (w >> k) & 1u64 == 1u64))
    by (bit_vector)
    requires b < 64, k < 64;
}

// At rydde bit b ændre kun bit b
proof fn lemma_clear_bit(w: u64, b: u64, k: u64)
    requires b < 64, k < 64,
    ensures bit_set(w & !(1u64 << b), k) == (k != b && bit_set(w,k)),
{
    assert(((w & !(1u64 << b)) >> k) & 1u64 == 1u64 <==> (k != b && (w >> k) & 1u64 == 1u64))
    by (bit_vector)
    requires b < 64, k < 64;
}


// Et ord, der er 0, har ingen bits sat
proof fn lemma_zero_word(k: u64)
        requires k < 64,
        ensures !bit_set(0u64, k),
{
    assert((0u64 >> k) & 1u64 != 1u64) by (bit_vector);
}

// Adressen på frames first_page .. first_page + num_pages
pub open spec fn region(first_page: int, num_pages: int) -> ISet<usize> {
    ISet::new(|a: usize| a % 4096 == 0 && first_page <= a / 4096 < first_page + num_pages)
}

    



// ========= Allokatoren =========
pub struct FrameAlloc {
        bitmap: [u64; WORDS],
        allocated: Ghost<ISet<usize>>,
}

impl FrameAlloc {
    spec fn frame_free(&self, i: int) -> bool {
        bit_set(self.bitmap@[i/64], (i % 64) as u64)
    }

    pub closed spec fn free(&self) -> ISet<usize> {
            ISet::new(|a: usize| a % 4096 == 0 && a / 4096 < MAX_FRAMES && self.frame_free((a / 4096) as int))
    }

    pub closed spec fn allocated(&self) -> ISet<usize> {
        self.allocated@
    }

    pub closed spec fn inv(&self) -> bool {
            forall|a: usize| #[trigger] self.allocated@.contains(a) ==>
            a % 4096 == 0
            && a / 4096 < MAX_FRAMES &&
            !self.frame_free((a / 4096) as int)
    }

    pub const fn new() -> (r: FrameAlloc)
        ensures
            r.inv(),
            r.free() == ISet::<usize>::empty(),
            r.allocated() == ISet::<usize>::empty(),
    {
            let r = FrameAlloc { bitmap: [0u64; WORDS], allocated: Ghost(ISet::empty()) };
            proof {
                assert forall|a:usize| !r.free().contains(a) by {
                    if a % 4096 == 0 && a / 4096 < MAX_FRAMES

        {
                    lemma_zero_word(((a / 4096) % 64) as u64);
                }
        }
        assert(r.free() =~= ISet::<usize>::empty());
        }
        r
    }

    pub fn add_region(&mut self, first_page: usize, num_pages: usize)
        requires
            old(self).inv(),
            first_page + num_pages <= MAX_FRAMES,
            old(self).allocated().disjoint(region(first_page as int, num_pages as int)),
        ensures
            final(self).inv(),
            final(self).allocated() == old(self).allocated(),
            final(self).free() == old(self).free().union(region(first_page as int, num_pages as int)),
            {
                let end = first_page + num_pages;
                let mut p = first_page;
                proof {
                    assert(self.free() =~= old(self).free().union(region(first_page as int, 0)));
            }
            while p < end
                invariant
                    first_page <= p <= end,
                    end == first_page + num_pages,
                    end <= MAX_FRAMES,
                    self.inv(),
                    self.allocated () == old(self).allocated(),
                    old(self).allocated().disjoint(region(first_page as int, num_pages as int)),
                    self.free() == old(self).free().union(region(first_page as int, p - first_page )),
                    decreases end - p,
                {
                    let ghost before = *self;
                    let wi = p / 64;
                    let b = (p % 64) as u64;
                    let w = self.bitmap[wi];
                    self.bitmap[wi] = w | (1u64 << b);
                    proof {
                    assert forall|i: int| 0 <= i < MAX_FRAMES implies #[trigger] self.frame_free(i) == (i == p || before.frame_free(i)) by {
                    lemma_set_bit(w, b, (i % 64) as u64);
                    }
                    let f = (p * 4096) as usize;
                    assert(f / 4096 == p && f % 4096 == 0);
                    assert forall|a: usize| #[trigger] self.allocated@.contains(a) implies a % 4096 == 0 && a / 4096 < MAX_FRAMES &&
                    !self.frame_free((a / 4096) as int) by { 
    assert(old(self).allocated().contains(a));

    assert(!region(first_page as int, num_pages as int).contains(a));
                }
                assert(self.free()=~= before.free().insert(f));
                assert(self.free() =~= old(self).free().union(region(first_page as int, p + 1 - first_page)));
                }
                p = p + 1;
            }
    }

pub fn alloc(&mut self) -> (r: Option<usize>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            match r {
                Some(f) => {
                    &&& f % 4096 == 0
                    &&&
                    old(self).free().contains(f)
                    &&&
                    !old(self).allocated().contains(f)
                    &&&
                    final(self).free() == old(self).free().remove(f)
                    &&&
                    final(self).allocated() ==
                    old(self).allocated().insert(f)
                    },
                    None => {
                        &&& old(self).free()
                        == ISet::<usize>::empty()
                    &&&
                    *final(self) == *old(self)
                    },
                },
        {
        let mut i: usize = 0;
        while i < WORDS && self.bitmap[i] == 0
            invariant
                0 <= i <= WORDS,
                forall|j: int| 0 <= j < i ==> self.bitmap@[j] == 0u64,
                decreases WORDS - i,
            {
                i = i + 1;
            }
            if i == WORDS {
                proof {
                    assert forall|a: usize| !self.free().contains(a) by {
    if a % 4096 == 0 && a / 4096 < MAX_FRAMES {
        let k = (a / 4096) as int;
    assert(self.bitmap@[k/64] == 0u64);
    lemma_zero_word((k % 64) as u64);
            }
        }
        assert(self.free() =~= ISet::<usize>::empty());
            }
        return None;
    }
        let ghost before = *self;
        let w = self.bitmap[i];
        proof {
    axiom_u64_trailing_zeros(w); }
        let b = w.trailing_zeros() as u64;
        let idx = i * 64 + b as usize;
        let f = idx * 4096;
        self.bitmap[i] = w & !(1u64 << b);
        self.allocated = Ghost(self.allocated@.insert(f));
            proof {
                assert(f / 4096 == idx && f % 4096 == 0);
                assert(idx / 64 == i && idx % 64 == b);
                assert(before.frame_free(idx as int));

                assert forall|k: int| 0 <= k < MAX_FRAMES implies #[trigger]
    self.frame_free(k) == (k!= idx && before.frame_free(k)) by {
        lemma_clear_bit(w, b, (k % 64) as u64);
                }

        assert(before.free().contains(f));
        assert(!before.allocated@.contains(f));
        assert(self.free()=~= before.free().remove(f));
        }
        Some(f)
    }

pub fn dealloc(&mut self, frame: usize) -> (ok: bool)
        requires
            old(self).inv(),
            old(self).allocated().contains(frame),
        ensures
            final(self).inv(),
            ok,
            final(self).free() == old(self).free().insert(frame),
            final(self).allocated() == old(self).allocated().remove(frame),
            {
                if frame % 4096 != 0 || frame / 4096 >= MAX_FRAMES {
                    return false;
                }
                let idx = frame / 4096;
                let wi = idx / 64;
                let b = (idx %  64) as u64;
                let w = self.bitmap[wi];
                if (w >> b) & 1u64 == 1u64 {
                    return false;
                }
                let ghost before = *self;
                self.bitmap[wi] = w | (1u64 << b);
                self.allocated = Ghost(self.allocated@.remove(frame));
                    proof {
                        assert forall|i: int| 0 <= i < MAX_FRAMES implies
                        #[trigger] self.frame_free(i) == (i == idx || before.frame_free(i)) by {
                            lemma_set_bit(w, b, (i % 64) as u64);
                            }
                assert forall|a: usize|
                #[trigger] self.allocated@.contains(a)
                implies
                    a % 4096 == 0 && a / 4096 < MAX_FRAMES && !self.frame_free((a / 4096) as int) by {
                        assert(before.allocated@.contains(a));
                            assert(a != frame);
                        }
                        assert(self.free() =~= before.free().insert(frame));
                            }
                        true
                    }

}

fn main() {
    let mut a = FrameAlloc::new();
    a.add_region(1, 4);
    assert(region(1, 4).contains(4096usize));

assert(a.free().contains(4096usize));
    let f1 = a.alloc();
    assert(f1.is_some());
    let f2 = a.alloc();
    assert(f1 != f2 || f2.is_none());
    let f1 = f1.unwrap();
    let ok = a.dealloc(f1);
    assert(ok);
    assert(a.free().contains(f1));
    let f3 = a.alloc();
    assert(f3.is_some());
}

} // verus!
