// A `Scope` value refers to an array (A) or object (O).
// It is used together with `Stack` to track if arrays or objects are
// currently en- or decoded. The boolean value is `false` if no elements
// have been encountered yet and `true` otherwise.

#[derive(Debug, Copy, Clone)]
pub enum Scope {
    A(bool), // Array
    O(bool), // Object
}

#[derive(Debug, Clone)]
pub struct Stack(Vec<Scope>);

impl Stack {
    pub fn new() -> Stack {
        Stack(Vec::new())
    }

    pub fn push(&mut self, s: Scope) {
        self.0.push(s)
    }

    pub fn pop(&mut self) -> Option<Scope> {
        self.0.pop()
    }

    pub fn top(&self) -> Option<Scope> {
        self.0.last().map(|x| *x)
    }

    pub fn set(&mut self) {
        self.0.last_mut().map(|x| match *x {
            Scope::A(_) => *x = Scope::A(true),
            Scope::O(_) => *x = Scope::O(true),
        });
    }
}
