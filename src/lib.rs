use std::fs;
use std::io::BufReader;
use std::path::Path;
use utf8_chars::BufReadCharsExt;

pub struct Source<A: 'static>(Box<dyn FnOnce() -> Option<(A, Source<A>)> + 'static>);

impl<A: 'static> Source<A> {
    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Option<A> {
        let original = std::mem::replace(self, Source::empty());
        match original.0() {
            Some((next_element, next_source)) => {
                *self = next_source;
                Some(next_element)
            }
            None => None,
        }
    }

    pub fn has_next(&mut self) -> bool {
        match self.next() {
            Some(a) => {
                let original = std::mem::replace(self, Source::empty());
                *self = original.prepend(a);
                true
            }
            None => false,
        }
    }

    pub fn new<F: FnMut() -> Option<A> + 'static>(mut function: F) -> Source<A> {
        Source(Box::new(move || {
            function().map(|next| (next, Source::new(function)))
        }))
    }

    pub fn empty() -> Source<A> {
        Source(Box::new(|| None))
    }

    pub fn single(a: A) -> Source<A> {
        Source(Box::new(|| Some((a, Source::empty()))))
    }

    pub fn map<B, F: FnMut(A) -> B + 'static>(mut self, mut function: F) -> Source<B> {
        #[allow(clippy::redundant_closure)]
        Source::new(move || self.next().map(|x| function(x)))
    }

    pub fn filter<F: FnMut(&A) -> bool + 'static>(mut self, mut function: F) -> Source<A> {
        Source::new(move || loop {
            match self.next() {
                Some(a) if function(&a) => return Some(a),
                Some(_) => {}
                None => return None,
            }
        })
    }

    pub fn fold<Accumulator, F: FnMut(Accumulator, A) -> Accumulator>(
        self,
        initial: Accumulator,
        mut function: F,
    ) -> Accumulator {
        let mut accumulator = initial;
        for a in self {
            accumulator = function(accumulator, a);
        }
        accumulator
    }

    pub fn flat_map<B, Next: FnMut(A) -> Source<B> + 'static>(self, next: Next) -> Source<B> {
        self.map(next).flatten()
    }

    pub fn concat(self, other: Source<A>) -> Source<A> {
        Source(Box::new(move || match self.0() {
            Some((a, next)) => Some((a, next.concat(other))),
            None => other.0(),
        }))
    }

    pub fn append(self, last: A) -> Source<A> {
        self.concat(Source::single(last))
    }

    pub fn prepend(self, head: A) -> Source<A> {
        Source(Box::new(|| Some((head, self))))
    }

    pub fn count<F: Fn(A) -> bool>(self, predicate: F) -> i32 {
        self.fold(0, |count, a| if predicate(a) { count + 1 } else { count })
    }
}

impl<A, I: Iterator<Item = A> + 'static> From<I> for Source<A> {
    fn from(mut iterator: I) -> Self {
        Source::new(move || iterator.next())
    }
}

impl<A> Source<Source<A>> {
    pub fn flatten(mut self) -> Source<A> {
        let mut current = Source::empty();
        Source::new(move || loop {
            match current.next() {
                Some(a) => return Some(a),
                None => match self.next() {
                    Some(next_chunk) => {
                        current = next_chunk;
                    }
                    None => return None,
                },
            }
        })
    }
}

impl<A: Clone> Source<A> {
    pub fn peek(&mut self) -> Option<A> {
        match self.next() {
            Some(a) => {
                let original = std::mem::replace(self, Source::empty());
                *self = original.prepend(a.clone());
                Some(a)
            }
            None => None,
        }
    }

    pub fn replicate(n: u32, element: A) -> Source<A> {
        let mut counter = 0;
        Source::new(move || {
            if counter < n {
                counter += 1;
                Some(element.clone())
            } else {
                None
            }
        })
    }
}

impl Source<char> {
    pub fn read_utf8_file(file: &Path) -> Result<Source<char>, std::io::Error> {
        let mut file = BufReader::new(fs::File::open(file)?);
        Ok(Source::new(move || {
            file.read_char().expect("utf8 decoding error")
        }))
    }
}

impl<Snippet: Into<Box<str>>> Source<Snippet> {
    pub fn join<Separator: Into<Box<str>>>(self, separator: Separator) -> String {
        let separator: &str = &separator.into();
        let mut first = true;
        let mut result = "".to_string();
        for string in self {
            if !first {
                result.push_str(separator);
            } else {
                first = false;
            }
            result.push_str(&string.into());
        }
        result
    }
}

impl<A> IntoIterator for Source<A> {
    type Item = A;
    type IntoIter = SourceIterator<A>;

    fn into_iter(self) -> SourceIterator<A> {
        SourceIterator(self)
    }
}

pub struct SourceIterator<A: 'static>(Source<A>);

impl<A> Iterator for SourceIterator<A> {
    type Item = A;

    fn next(&mut self) -> Option<A> {
        self.0.next()
    }
}

#[macro_export]
macro_rules! source {
    ($($x:expr),*) => {
        $crate::Source::from(vec![$($x),*].into_iter())
    };
    ($($x:expr,)*) => {
        source![$($x),*]
    };
    ($element:expr; $n:expr) => {
        $crate::Source::replicate($n, $element)
    };
}

impl<A: std::fmt::Debug> Source<A> {
    pub fn debug(self) -> String {
        format!("source![{}]", self.map(|x| format!("{:?}", x)).join(", "))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    impl<A> Source<A> {
        pub fn to_vec(self) -> Vec<A> {
            self.into_iter().collect()
        }
    }

    mod conversions {
        use super::*;

        #[test]
        fn allows_to_convert_from_iterator() {
            let iter = vec![1, 2, 3].into_iter();
            let from_next = Source::from(iter);
            assert_eq!(from_next.to_vec(), vec![1, 2, 3]);
        }

        #[test]
        fn allows_to_convert_into_iterator() {
            let source = source!(1, 2, 3).into_iter();
            assert_eq!(source.collect::<Vec<_>>(), vec![1, 2, 3]);
        }
    }

    mod source_macro {
        use super::*;

        #[test]
        fn allows_to_convert_from_elements() {
            let source: Source<i32> = source![1, 2, 3];
            assert_eq!(source.to_vec(), vec![1, 2, 3]);
        }

        #[test]
        fn allows_to_create_empty_sources() {
            let source: Source<i32> = Source::empty();
            assert_eq!(source.to_vec(), vec![]);
        }

        #[test]
        fn allows_to_create_sources_with_one_element() {
            let source = Source::single("foo");
            assert_eq!(source.to_vec(), vec!["foo"]);
        }

        #[test]
        fn allows_to_trailing_commas() {
            let source: Source<i32> = source![1, 2, 3,];
            assert_eq!(source.to_vec(), vec![1, 2, 3]);
        }

        #[test]
        fn allows_to_replicate_a_given_element() {
            let source: Source<i32> = source![42; 3];
            assert_eq!(source.to_vec(), vec![42, 42, 42]);
        }
    }

    mod debug {
        use super::*;

        #[test]
        fn debug_converts_into_source_macro() {
            assert_eq!(source![1, 2, 3].debug(), "source![1, 2, 3]");
            let empty: Source<i32> = source![];
            assert_eq!(empty.debug(), "source![]");
        }

        #[test]
        fn debug_uses_debug() {
            assert_eq!(source!["foo", "bar"].debug(), r#"source!["foo", "bar"]"#);
        }
    }

    mod has_next {
        use super::*;

        #[test]
        fn returns_true_for_non_empty_sources() {
            let mut source = source!["foo"];
            assert_eq!(source.has_next(), true);
        }

        #[test]
        fn returns_false_when_all_elements_are_consumed() {
            let mut source = source!["foo"];
            source.next();
            assert_eq!(source.has_next(), false);
        }

        #[test]
        fn returns_false_for_empty_sources() {
            let mut source: Source<()> = source![];
            assert_eq!(source.has_next(), false);
        }

        #[test]
        fn does_not_modify_the_source_elements() {
            let mut source = source!["foo"];
            source.has_next();
            assert_eq!(source.to_vec(), vec!["foo"]);
        }
    }

    #[test]
    fn map_works() {
        let from_next: Source<i32> = source![1, 2, 3];
        let mapped = from_next.map(|x| x.pow(2));
        assert_eq!(vec![1, 4, 9], mapped.to_vec());
    }

    #[test]
    fn filter_works() {
        let source = Source::from(1..6).filter(|x| x % 2 == 1);
        assert_eq!(source.to_vec(), vec![1, 3, 5]);
    }

    #[test]
    fn fold_works() {
        let sum = Source::from(1..6).fold(0, |sum: i32, a| sum + a);
        assert_eq!(sum, 15);
    }

    #[test]
    fn flatten_works() {
        let flattened = source!["foo", "bar"]
            .map(|x| Source::from(x.chars()))
            .flatten();
        assert_eq!(vec!['f', 'o', 'o', 'b', 'a', 'r'], flattened.to_vec());
    }

    #[test]
    fn flatmap_works() {
        let source = source!["foo", "bar"].flat_map(|x| Source::from(x.chars()));
        assert_eq!(vec!['f', 'o', 'o', 'b', 'a', 'r'], source.to_vec());
    }

    #[test]
    fn concat_works() {
        let mut source = source!["foo", "bar"];
        source = source.concat(source!["baz"]);
        assert_eq!(vec!["foo", "bar", "baz"], source.to_vec());
    }

    #[test]
    fn append_works() {
        let mut source = source!["foo", "bar"];
        source = source.append("baz");
        assert_eq!(vec!["foo", "bar", "baz"], source.to_vec());
    }

    #[test]
    fn prepend_works() {
        let source = source!["bar", "baz"].prepend("foo");
        assert_eq!(vec!["foo", "bar", "baz"], source.to_vec());
    }

    mod peek {
        use super::*;

        #[test]
        fn peek_works() {
            let mut source = source!["foo", "bar"];
            assert_eq!(source.peek(), Some("foo"));
            assert_eq!(vec!["foo", "bar"], source.to_vec());
        }

        #[test]
        fn allows_to_peek_ahead() {
            let mut source = Source::from("x".chars());
            assert_eq!(source.peek(), Some('x'));
        }

        #[test]
        fn peeking_does_not_consume_chars() {
            let mut source = Source::from("x".chars());
            source.peek();
            assert_eq!(source.next(), Some('x'));
        }

        #[test]
        fn peeking_works_twice() {
            let mut source = Source::from("ab".chars());
            source.peek();
            assert_eq!(source.peek(), Some('a'));
        }

        #[test]
        fn peeking_works_after_next() {
            let mut source = Source::from("ab".chars());
            source.next();
            assert_eq!(source.peek(), Some('b'));
        }
    }

    #[test]
    fn count_works() {
        let source = source![1, 2, 3, 4, 5, 6, 7];
        assert_eq!(source.count(|x| x > 3), 4);
    }

    mod join {
        use super::*;

        #[test]
        fn works() {
            let source = source!("foo", "bar");
            assert_eq!(source.join("#"), "foo#bar");
        }

        #[test]
        fn works_with_both_str_and_string() {
            let str_source: Source<&str> = source!();
            str_source.join("");
            let str_source: Source<&str> = source!();
            str_source.join("".to_string());
            let string_source: Source<String> = source!();
            string_source.join("");
            let string_source: Source<String> = source!();
            string_source.join("".to_string());
        }

        #[test]
        fn works_with_empty_inputs() {
            assert_eq!(source!("", "foo").join("#"), "#foo");
            assert_eq!(source!("foo", "").join("#"), "foo#");
            assert_eq!(source!("", "foo", "").join("#"), "#foo#");
        }
    }
}
